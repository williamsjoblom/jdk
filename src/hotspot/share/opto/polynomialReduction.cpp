#include "precompiled.hpp"
#include "opto/polynomialReduction.hpp"
#include "opto/loopnode.hpp"
#include "opto/node.hpp"
#include "opto/addnode.hpp"
#include "opto/memnode.hpp"
#include "opto/mulnode.hpp"
#include "opto/connode.hpp"
#include "opto/type.hpp"
#include "opto/vectornode.hpp"
#include "opto/callnode.hpp"
#include "opto/output.hpp"
#include "utilities/powerOfTwo.hpp"
#include "opto/opaquenode.hpp"
#include "utilities/align.hpp"

/****************************************************************
 * Forward declarations.
 ***************************************************************/
VectorNode *make_vector(PhaseIdealLoop *phase, Node *init, juint vec_size);
VectorNode *make_vector(PhaseIdealLoop *phase, jint init, juint vec_size);

/****************************************************************
 * Tracing.
 ****************************************************************/
enum TraceOpts {
  NoTraceOpts = 0,
  MinCond = 1 << 0,
  Match = 1 << 1,
  Rewrite = 1 << 2,
  Success = 1 << 3,
  Failure = 1 << 4,
  FinalReport = Success | Failure,
  Candidates = 1 << 5,
  AllTraceOpts = 0xFFFFFFFF
};

// Maximum search depth for `find_node`.
//
// TODO: The current value of `20` is most likely too high.
const uint MAX_SEARCH_DEPTH = 20;

// Enabled traces
const int TRACE_OPTS = Success | Failure;

#ifndef PRODUCT
#define TRACE(OPT, BODY)                                                \
  do {                                                                  \
    if (((OPT) & TRACE_OPTS) != 0) {                                    \
      BODY;                                                             \
    }                                                                   \
  } while(0)
#else
#define TRACE(OPT, BODY)                        \
  do { } while (0)
#endif

/****************************************************************
 * Predicates.
 ****************************************************************/
bool is_array_ptr(Node *n) {
  return n->is_Type() && n->as_Type()->type()->isa_aryptr() != NULL;
}

bool is_primitive_load(Node *n) {
  return n->is_Load() && is_java_primitive(n->bottom_type()->basic_type());
}

// Is this an binary operation.
bool is_binop(Node *n) {
  switch (n->Opcode()) {
  case Op_AddI:
  case Op_SubI:
  case Op_MulI:
  case Op_DivI:
  case Op_LShiftI:
    return true;
  default:
    return false;
  }
}

/****************************************************************
 * Minimum matching condition.
 ****************************************************************/
PhiNode *find_recurrence_phi(CountedLoopNode *cl) {
  // Find _the_ phi node connected with a control edge from the given
  // CountedLoop (excluding the phi node associated with the induction
  // variable).
  Node *induction_phi = cl->phi();
  if (induction_phi == NULL) return NULL;

  Node *recurrence_phi = NULL;
  for (DUIterator it = cl->outs(); cl->has_out(it); it++) {
    Node *n = cl->out(it);
    // NOTE: maybe check that the edge we just followed is a control
    // edge?
    if (n->is_Phi() && n != induction_phi &&
        is_java_primitive(n->bottom_type()->basic_type())) {
      // Only allow loops with one cross-iteration dependecy for now:
      if (recurrence_phi != NULL) {
        TRACE(MinCond, {
            tty->print_cr("Multiple recurrence phi's found. Aborting...");
            tty->print("  First:  "); recurrence_phi->dump("\n");
            tty->print("  Second: "); n->dump("\n");
            tty->print("  IV:     "); induction_phi->dump("\n");
          });
        return NULL;
      }

      recurrence_phi = n;
    }
  }

  return recurrence_phi != NULL ? recurrence_phi->as_Phi() : NULL;
}

// DFS following DU-edges searching for a member of `nodes`. Depth
// limited by `MAX_SEARCH_DEPTH`.

// Do a depth first search following outgoing edges until a member of
// `nodes` is found. This node is then returned.
Node *find_nodes(Node *start, Node_List &nodes, Unique_Node_List &visited, uint depth=0) {
  if (depth >= MAX_SEARCH_DEPTH || visited.member(start)) return NULL;
  if (nodes.contains(start)) return start;

  visited.push(start);

  for (DUIterator it = start->outs(); start->has_out(it); it++) {
    Node *n = start->out(it);
    Node *result = find_nodes(n, nodes, visited, depth + 1);
    if (result != NULL) return result;
  }

  return NULL;
}

// TODO: most likely too slow to be run on EVERY CountedLoop. We
// should probably replace the DFS in `find_nodes` with a BFS, reduce
// `MAX_SEARCH_DEPTH`, or come up with a new solution all together.
Node *find_rhs(PhiNode *reduction_phi) {
  return reduction_phi->in(2);

  Node_List inputs;
  for (uint i = PhiNode::Input; i < reduction_phi->len(); i++) {
    inputs.push(reduction_phi->in(i));
  }

  Unique_Node_List visited;
  Node *bottom = find_nodes(reduction_phi, inputs, visited);

  return bottom;
}

/****************************************************************
 * Match references.
 ****************************************************************/
class MatchRefs : public ResourceObj {
  static const int MAX_REFS = 32;
  int _n;
  Node *_refs[MAX_REFS];

public:
  MatchRefs(int n) : _n(n) {
    assert(n <= MAX_REFS, "maximum number of references reached");
    for (int i = 0; i < n; ++i) _refs[i] = NULL;
  }

  inline Node *&operator[](int i) {
    guarantee(i < _n, "out of bounds");
    return _refs[i];
  }
};

/****************************************************************
 * Pattern matching.
 ****************************************************************/

#define ANY (Pattern*)NULL
const bool TRACE_MATCHING = true;

class Pattern : public ResourceObj {
protected:
  static const int NO_REF = -1;
  inline void set_ref(Node *n, MatchRefs &refs) {
    if (_ref != NO_REF) refs[_ref] = n;
  }
public:
  int _ref;

  Pattern(int ref) : _ref(ref) {}
  virtual ~Pattern() {}
  virtual bool match(Node *n, MatchRefs& refs) = 0;
};

// TODO: Make Opcode a field instead of a template parameter.
template<uint NSubpatterns>
class OpcodePattern : public Pattern {
public:
  int _opcode;
  Pattern* _subpatterns[NSubpatterns];

  OpcodePattern(int opcode, int ref=NO_REF)
    : Pattern(ref), _opcode(opcode) {
    assert(NSubpatterns == 0, "expected");
  }

  OpcodePattern(int opcode, Pattern *p0, int ref=NO_REF)
    : Pattern(ref), _opcode(opcode) {
    assert(NSubpatterns == 1, "expected");
    _subpatterns[0] = p0;
  }

  OpcodePattern(int opcode, Pattern *p0, Pattern *p1, int ref=NO_REF)
    : Pattern(ref), _opcode(opcode) {
    assert(NSubpatterns == 2, "expected");
    _subpatterns[0] = p0;
    _subpatterns[1] = p1;
  }

  OpcodePattern(int opcode, Pattern *p0, Pattern *p1, Pattern *p2, int ref=NO_REF)
    : Pattern(ref), _opcode(opcode) {
    assert(NSubpatterns == 3, "expected");
    _subpatterns[0] = p0; _subpatterns[1] = p1;
    _subpatterns[2] = p2;
  }

  OpcodePattern(int opcode, Pattern *p0, Pattern *p1, Pattern *p2, Pattern *p3, int ref=NO_REF)
    : Pattern(ref), _opcode(opcode) {
    assert(NSubpatterns == 4, "expected");
    _subpatterns[0] = p0; _subpatterns[1] = p1;
    _subpatterns[2] = p2; _subpatterns[3] = p3;
  }

  bool match(Node *n, MatchRefs &refs) {
    if (n->Opcode() != _opcode) {
      set_ref(NULL, refs);
      return false;
    }

    for (uint i = 0; i < (NSubpatterns < n->req() ? NSubpatterns : n->req()); i++) {
      Node *next = n->in(i);
      Pattern *sp = _subpatterns[i];
      if (sp != ANY) {
        if (next == NULL || !sp->match(next, refs)) {
          TRACE(Match, {
              tty->print("[OpcodePattern] Matching failed for in(%d)", i);
              n->dump();
              next != NULL ? next->dump("  ") : tty->print("  NULL");
              tty->print_cr("");
            });
          set_ref(NULL, refs);
          return false;
        }
      }
    }

    set_ref(n, refs);
    return true;
  }
};


class OrPattern : public Pattern {
public:
  // Only match this exact node.
  Pattern *_p0;
  Pattern *_p1;

  OrPattern(Pattern* p0, Pattern *p1)
    : Pattern(NO_REF), _p0(p0), _p1(p1) {};

  bool match(Node *n, MatchRefs &refs) {
    return _p0->match(n, refs) || _p1->match(n, refs);
  }
};

class ExactNodePattern : public Pattern {
public:
  // Only match this exact node.
  Node *_n;

  ExactNodePattern(Node *n) : Pattern(NO_REF), _n(n) {};

  bool match(Node *n, MatchRefs &refs) {
    return n == _n;
  }
};

typedef bool (*NodePred)(Node *);
class PredPattern : public Pattern {
private:
  NodePred _pred;
public:
  PredPattern(NodePred pred, int ref=NO_REF) : Pattern(ref), _pred(pred) {}

  bool match(Node *n, MatchRefs &refs) {
    if (_pred(n)) {
      set_ref(n, refs);
      return true;
    } else {
      set_ref(NULL, refs);
      return false;
    }
  }
};

template<uint NSubpatterns>
class Pred2Pattern : public Pattern {
public:
  NodePred _pred;
  Pattern* _subpatterns[NSubpatterns];

  Pred2Pattern(NodePred pred, int ref=NO_REF)
    : Pattern(ref), _pred(pred) {
    assert(NSubpatterns == 0, "expected");
  }

  Pred2Pattern(NodePred pred, Pattern *p0, int ref=NO_REF)
    : Pattern(ref), _pred(pred) {
    assert(NSubpatterns == 1, "expected");
    _subpatterns[0] = p0;
  }

  Pred2Pattern(NodePred pred, Pattern *p0, Pattern *p1, int ref=NO_REF)
    : Pattern(ref), _pred(pred) {
    assert(NSubpatterns == 2, "expected");
    _subpatterns[0] = p0;
    _subpatterns[1] = p1;
  }

  Pred2Pattern(NodePred pred, Pattern *p0, Pattern *p1, Pattern *p2, int ref=NO_REF)
    : Pattern(ref), _pred(pred) {
    assert(NSubpatterns == 3, "expected");
    _subpatterns[0] = p0; _subpatterns[1] = p1;
    _subpatterns[2] = p2;
  }

  Pred2Pattern(NodePred pred, Pattern *p0, Pattern *p1, Pattern *p2, Pattern *p3, int ref=NO_REF)
    : Pattern(ref), _pred(pred) {
    assert(NSubpatterns == 4, "expected");
    _subpatterns[0] = p0; _subpatterns[1] = p1;
    _subpatterns[2] = p2; _subpatterns[3] = p3;
  }

  bool match(Node *n, MatchRefs &refs) {
    if (!_pred(n)) {
      set_ref(NULL, refs);
      return false;
    }

    for (uint i = 0; i < n->req() && i < NSubpatterns; i++) {
      Node *next = n->in(i);
      Pattern *sp = _subpatterns[i];
      if (sp != ANY) {
        if (next == NULL || !sp->match(next, refs)) {
          TRACE(Match, {
              tty->print("[Pred2Pattern] Matching failed for in(%d):", i);
              n->dump();
              next != NULL ? next->dump("  ") : tty->print("  NULL");
              tty->print_cr("");
            });
          set_ref(NULL, refs);
          return false;
        }
      }
    }

    set_ref(n, refs);
    return true;
  }
};


// Unconditionally matches a node, saving it as a ref.
class CapturePattern : public Pattern {
public:
  CapturePattern(int ref) : Pattern(ref) {}
  bool match(Node *n, MatchRefs &refs) {
    set_ref(n, refs);
    return true;
  }
};

/****************************************************************
 * Pattern instances.
 ****************************************************************/

struct PatternInstance : ResourceObj {
  // Generate Node.
  virtual Node *generate(PhaseIdealLoop *phase, uint vlen) = 0;
  virtual Node *result() = 0;
};

// Array read pattern instance.
struct ArrayLoadPattern : PatternInstance {
  // Basic type of loaded value.
  BasicType _bt;

  // Load node.
  Node *_load;

  // Load control dep.
  Node *_load_ctrl;

  // Node indexing the array.
  Node *_index;

  // Array being indexed.
  Node *_array_ptr;

  // Memory state.
  Node *_memory;

  // Node producing the result.
  Node *_result;

  // Size, in bytes, of each element.
  jint _elem_byte_size;

  // Base offset of the array.
  jlong _base_offset;

  virtual Node *generate(PhaseIdealLoop *phase, uint vlen) {
    LoadNode *load = _load->as_Load();
    BasicType load_type = _bt;
    BasicType elem_type = load->memory_type();

    TRACE(Rewrite, {
        tty->print_cr("load: %s, elem: %s", type2name(load_type),
                      type2name(elem_type));
      });

    // No implicit cast.
    if (elem_type == load_type) {
      Node *arr = LoadVectorNode::make(
        _load->Opcode(), _load->in(LoadNode::Control),
        _memory, _load->in(LoadNode::Address),
        _load->adr_type(), vlen, load_type);
      phase->igvn().register_new_node_with_optimizer(arr, NULL);
      return arr;
    } else {
      Node *arr = LoadVectorNode::make_promotion(
        _load->Opcode(), _load->in(LoadNode::Control),
        _memory, _load->in(LoadNode::Address),
        _load->adr_type(), vlen, load_type);
      phase->igvn().register_new_node_with_optimizer(arr, NULL);
      return arr;
    }

    ShouldNotReachHere();
    return NULL;
  }

  virtual Node *result() {
    return _load;
  }
};

struct ScalarPattern : PatternInstance {
  Node *_scalar;

  virtual Node *generate(PhaseIdealLoop *phase, uint vlen) {
    return make_vector(phase, _scalar, vlen);
  }

  virtual Node *result() {
    return _scalar;
  }
};

struct BinOpPattern : PatternInstance {
  int _opcode;
  PatternInstance *_lhs, *_rhs;
  BasicType _bt;

  virtual Node *generate(PhaseIdealLoop *phase, uint vlen) {
    Node *lhs = _lhs->generate(phase, vlen);
    Node *rhs = _rhs->generate(phase, vlen);

    Node *result = VectorNode::make(_opcode, lhs, rhs, vlen, _bt);
    phase->igvn().register_new_node_with_optimizer(result);
    return result;
  }

  virtual Node *result() {
    ShouldNotCallThis();
    return NULL;
  }
};

struct LShiftPattern : BinOpPattern {
  virtual Node *generate(PhaseIdealLoop *phase, uint vlen) {
    assert(_opcode == Op_LShiftI, "sanity");
    assert(_rhs->result()->is_Con(), "not implemented");

    Node *lhs = _lhs->generate(phase, vlen);

    Node *multiplier = phase->igvn().intcon(1 << _rhs->result()->get_int());
    Node *result = new MulVINode(lhs, make_vector(phase, multiplier, vlen),
                                 TypeVect::make(T_INT, vlen));
    phase->igvn().register_new_node_with_optimizer(result);
    return result;
  }
};

struct ConMul {
  jint multiplier;
};

// Match `of` multiplied by a constant that has been rewritten as a
// shift and an add/sub.
bool match_shift_con_mul(Node *start, Node *of, ConMul &result) {
  enum {
    SHIFT_DISTANCE,
    SUB,
    ADD,
    N_REFS
  };

  Pattern *l_shift = new OpcodePattern<3>
    (Op_LShiftI,
     ANY,
     new ExactNodePattern(of),
     new OpcodePattern<0>(Op_ConI, SHIFT_DISTANCE));

  Pattern *shift_sub = new OpcodePattern<3>
    (Op_SubI,
     ANY,
     l_shift,
     new ExactNodePattern(of),
     SUB);

  Pattern *shift_add = new OpcodePattern<3>
    (Op_AddI,
     ANY,
     l_shift,
     new ExactNodePattern(of),
     ADD);

  Pattern *shift = new OrPattern(shift_sub, new OrPattern(shift_add, l_shift));

  MatchRefs refs(N_REFS);
  if (shift->match(start, refs)) {
    result.multiplier = (1 << refs[SHIFT_DISTANCE]->get_int());
    if (refs[SUB]) {
      result.multiplier--;
    } else if (refs[ADD]) {
      result.multiplier++;
    }

    return true;
  } else {
    TRACE(Match, {
        tty->print_cr("  origin shift_con_mul");
      });

    return false;
  }
}

bool match_trivial_con_mul(Node *start, Node *of, ConMul &result) {
  enum {
    MUL,
    N_REFS
  };

  Pattern *mul = new OpcodePattern<3>
    (Op_MulI,
     ANY,
     new ExactNodePattern(of),
     new OpcodePattern<0>(Op_ConI, MUL));

  MatchRefs refs(N_REFS);
  if (mul->match(start, refs)) {
    result.multiplier = refs[MUL]->get_int();
    return true;
  } else {
    return false;
  }
}

bool match_identity_con_mul(Node *start, Node *of, ConMul &result) {
  if (start == of) {
    result.multiplier = 1;
    return true;
  } else {
    TRACE(Match, {
        tty->print_cr("  origin identity_con_mul");
      });
    return false;
  }
}

// Match multiplication of `of` and a constant placing the constant in
// `result`.
bool match_con_mul(Node *start, Node *of, ConMul &result) {
  return
    match_identity_con_mul(start, of, result) ||
    match_shift_con_mul(start, of, result) ||
    match_trivial_con_mul(start, of, result);
}

// Match array read.
ArrayLoadPattern *match_array_read(Node *start, Node *idx) {
  ArrayLoadPattern *result = new ArrayLoadPattern();

  ResourceMark rm;

  enum {
    LOAD_NODE,
    LOAD_CTRL,
    ARRAY,
    MEMORY,
    IDX_SHIFT_DISTANCE,
    ARRAY_BASE_OFFSET,
    CAST_II,

    N_REFS
  };

  MatchRefs refs(N_REFS);
  Pattern *pre_shift = new OpcodePattern<2> // LShiftL: Left-hand side
    (Op_ConvI2L,
     ANY,                          // ConvI2L: Control
     new OpcodePattern<2> // ConvI2L: Data
     (Op_CastII,
      ANY,                         // CastII:  Control
      new ExactNodePattern(idx),   // CastII:  Index
      CAST_II));

  Pattern *shift = new OpcodePattern<3>  // AddP: Offset
    (Op_LShiftL,
     ANY,                           // LShiftL: Control
     pre_shift,
     new OpcodePattern<0>(Op_ConI, IDX_SHIFT_DISTANCE));

  Pattern *p = new Pred2Pattern<3>
    (is_primitive_load, // Match load nodes of primitive type.
     new CapturePattern(LOAD_CTRL),
     new CapturePattern(MEMORY),
     new OpcodePattern<4>
     (Op_AddP,
      ANY,
      ANY,
      new OpcodePattern<4>
      (Op_AddP,
       ANY,                            // AddP: Control
       ANY,                            // AddP: Base
       new PredPattern(is_array_ptr, ARRAY), // AddP: Address
       new OrPattern(shift, pre_shift)),
      new OpcodePattern<0>(Op_ConL, ARRAY_BASE_OFFSET)),
      LOAD_NODE);

  if (p->match(start, refs)) {
    result->_load_ctrl = refs[LOAD_CTRL];
    result->_load = refs[LOAD_NODE];
    result->_bt = result->_load->bottom_type()->basic_type();
    result->_index = idx;
    result->_result = start;
    result->_array_ptr = refs[ARRAY];
    result->_memory = refs[MEMORY];
    result->_elem_byte_size =
      1 << (refs[IDX_SHIFT_DISTANCE] != NULL
            ? refs[IDX_SHIFT_DISTANCE]->get_int()
            : 0);
    result->_base_offset = refs[ARRAY_BASE_OFFSET]->get_long();

    assert(result->_load_ctrl->isa_Proj(), "");
    return result;
  } else {
    TRACE(Match, {
        tty->print_cr("  origin array_read");
      });
    return NULL;
  }
}

PatternInstance *match(Node *start, Node *iv);

PatternInstance *match_binop(Node *start, Node *iv) {
  // Only accept binary operations without control dependence.
  if (!(is_binop(start) && start->in(0) == NULL)) return NULL;

  Node *lhs = start->in(1);
  Node *rhs = start->in(2);
  assert(lhs != NULL && rhs != NULL, "sanity");

  PatternInstance *lhs_p = match(lhs, iv);
  if (lhs_p == NULL) return NULL;
  PatternInstance *rhs_p = match(rhs, iv);
  if (rhs_p == NULL) return NULL;

  BinOpPattern *pi = start->Opcode() != Op_LShiftI
    ? new BinOpPattern()
    : new LShiftPattern();
  pi->_opcode = start->Opcode();
  pi->_lhs = lhs_p;
  pi->_rhs = rhs_p;
  pi->_bt = start->bottom_type()->array_element_basic_type();

  return pi;
}

PatternInstance *match_scalar(Node *start) {
  // NOTE: Assumes the scalar to be loop invariant. Presence of loop
  // variant scalars should exit idiom vectorization early. To account
  // for this, we currently only accept scalar constants.
  if (start->Opcode() == Op_ConI) {
    ScalarPattern *p = new ScalarPattern();
    p->_scalar = start;
    return p;
  } else {
    return NULL;
  }
}

PatternInstance *match(Node *start, Node *iv) {
  PatternInstance *pi;
  if (pi = match_array_read(start, iv))
    return pi;
  if (pi = match_binop(start, iv))
    return pi;
  if (pi = match_scalar(start))
    return pi;

  TRACE(Match, {
      tty->print_cr("Unable to find pattern instance.");
      tty->print("  "); start->dump(" start node");
    });

  return NULL;
}

/****************************************************************
 * Utility.
 ****************************************************************/

// Make int vector containing [init, init, ..., init]
VectorNode *make_vector(PhaseIdealLoop *phase, Node *init, juint vec_size) {
  // TODO: Make vector type depend on recurrence variable type.
  VectorNode *v = VectorNode::scalar2vector(init, vec_size, TypeInt::INT);
  phase->igvn().register_new_node_with_optimizer(v);
  return v;
}

// Make int vector containing [init, init, ..., init]
VectorNode *make_vector(PhaseIdealLoop *phase, jint init, juint vec_size) {
  ConNode *init_con = ConNode::make(TypeInt::make(init));
  phase->igvn().register_new_node_with_optimizer(init_con);
  return make_vector(phase, init_con, vec_size);
}

// Make 4 int vector containing [n^{vlen}, n^{vlen-1}, ..., n^1, n^0].
VectorNode *make_exp_vector(PhaseIdealLoop *phase, jint n, juint vlen) {
  assert(vlen == 4 || vlen == 8, "expected");

  if (0 <= n && n <= 1) {
    // [0^3, 0^2, 0^1, 0^0] = [0, 0, 0, 0] and
    // [1^3, 1^2, 1^1, 1^0] = [1, 1, 1, 1]
    return make_vector(phase, n, vlen);
  }

  // TODO: The following code need to be modified to support
  // big-endian systems, fixed by adjusting shift distances depending
  // on target endianness.
  if (vlen == 4) {
    ConNode *b = ConNode::make(TypeLong::make(((n * n * n)) | ((long)n * n << 32)));
    ConNode *a = ConNode::make(TypeLong::make(n | ((long)1 << 32)));
    VectorNode *con = VectorNode::scalars2vector(a, b);
    phase->igvn().register_new_node_with_optimizer(a);
    phase->igvn().register_new_node_with_optimizer(b);
    phase->igvn().register_new_node_with_optimizer(con);
    return con;
  } else if (vlen == 8) {
    // NOTE: Integer overflow is expected here:
    jlong a_value = n             | (((long)1)           << 32);
    jlong b_value = n*n*n         | (((long)n*n)         << 32);
    jlong c_value = n*n*n*n*n     | (((long)n*n*n*n)     << 32);
    jlong d_value = n*n*n*n*n*n*n | (((long)n*n*n*n*n*n) << 32);

    ConNode *a = ConNode::make(TypeLong::make(a_value));
    ConNode *b = ConNode::make(TypeLong::make(b_value));
    ConNode *c = ConNode::make(TypeLong::make(c_value));
    ConNode *d = ConNode::make(TypeLong::make(d_value));
    VectorNode *con_lo = VectorNode::scalars2vector(d, c);
    VectorNode *con_hi = VectorNode::scalars2vector(b, a);
    VectorNode *con = VectorNode::scalars2vector(con_lo, con_hi);
    phase->igvn().register_new_node_with_optimizer(a);
    phase->igvn().register_new_node_with_optimizer(b);
    phase->igvn().register_new_node_with_optimizer(c);
    phase->igvn().register_new_node_with_optimizer(d);
    phase->igvn().register_new_node_with_optimizer(con_lo);
    phase->igvn().register_new_node_with_optimizer(con_hi);

    return con;
  }

  ShouldNotReachHere();
  return NULL;
}

// n^exp
jint my_pow(jint n, jint exp) {
  jint result = 1;
  while (exp--) {
    result *= n;
  }
  return result;
}

// Build vector array load from a matched ArrayRead.
Node *build_array_load(PhaseIdealLoop *phase, ArrayLoadPattern& array_read, uint vlen) {
  LoadNode *load = array_read._load->as_Load();
  BasicType load_type = array_read._bt;
  BasicType elem_type = load->memory_type();

  TRACE(Rewrite, {
      tty->print_cr("load: %s, elem: %s", type2name(load_type),
                    type2name(elem_type));
    });

  // No implicit cast.
  if (elem_type == load_type) {
     Node *arr = LoadVectorNode::make(
        array_read._load->Opcode(), array_read._load->in(LoadNode::Control),
        array_read._memory, array_read._load->in(LoadNode::Address),
        array_read._load->adr_type(), vlen, load_type);
     phase->igvn().register_new_node_with_optimizer(arr, NULL);
     return arr;
  } else {
    Node *arr = LoadVectorNode::make_promotion(
        array_read._load->Opcode(), array_read._load->in(LoadNode::Control),
        array_read._memory, array_read._load->in(LoadNode::Address),
        array_read._load->adr_type(), vlen, load_type);
    phase->igvn().register_new_node_with_optimizer(arr, NULL);
    return arr;
  }

  ShouldNotReachHere();
  return NULL;
}


// Find the pre loop end of the given main loop.
CountedLoopEndNode *find_pre_loop_end(CountedLoopNode *main) {
  Node *pre_false = main->skip_predicates()->in(0)->in(0);
  assert(pre_false->is_IfFalse(), "sanity");
  Node *pre_end = pre_false->in(0);
  assert(pre_end->is_CountedLoopEnd(), "sanity");
  return pre_end->as_CountedLoopEnd();
}

// Find the pre loop of the given main loop.
CountedLoopNode *find_pre_loop(CountedLoopNode *main) {
  CountedLoopEndNode *pre_loop_end = find_pre_loop_end(main);
  CountedLoopNode *pre_loop = pre_loop_end->loopnode()->as_CountedLoop();
  assert(pre_loop->is_pre_loop(), "sanity");
  return pre_loop;
}

// Find zero trip CmpNode for the given loop.
CmpNode *zero_trip_test(CountedLoopNode *loop) {
  return loop->skip_predicates()->in(0)->in(1)->in(1)->as_Cmp();
}

/****************************************************************
 * Loop patching.
 ****************************************************************/
// Split loop into a pre, main, and post loop and adjust zero trip
// guard for the main loop to account for the vector length.
Node *split_loop(IdealLoopTree *lpt, PhaseIdealLoop *phase,
                CountedLoopNode *cl, juint vlen) {
  Node_List old_new;
  if (cl->is_normal_loop()) {
    phase->insert_pre_post_loops(lpt, old_new, false);
  }

  Node *zero_cmp = zero_trip_test(cl);
  Node *zero_iv = zero_cmp->in(1);
  Node *zero_opaq = zero_cmp->in(2);
  assert(zero_opaq->outcnt() == 1, "opaq should only have one user");
  Node *zero_opaq_ctrl = phase->get_ctrl(zero_opaq);

  Node *adjusted_limit = new SubINode(zero_opaq, phase->igvn().intcon(vlen));
  phase->igvn().register_new_node_with_optimizer(adjusted_limit);
  phase->igvn().replace_input_of(zero_cmp, 2, adjusted_limit);

  return adjusted_limit;
}

// Set stride of the given loop.
void set_stride(CountedLoopNode *cl, PhaseIdealLoop *phase, jint new_stride) {
  assert(cl->stride_is_con(), "setting stride for non const stride loop");

  ConNode *stride = ConNode::make(TypeInt::make(new_stride));
  phase->igvn().register_new_node_with_optimizer(stride);

  Node *incr = cl->incr();
  if (incr != NULL && incr->req() == 3) {
    //phase->igvn().replace_node(cl->stride(), stride);
    phase->igvn().replace_input_of(incr, 2, stride);
  } else {
    ShouldNotReachHere();
  }
}

// Adjust loop limit to account for the vector length.
void adjust_limit(CountedLoopNode *cl, PhaseIdealLoop *phase, Node *adjusted_limit) {
  // WARNING: (limit - stride) may underflow!!!
  const uint LIMIT = 2;
  Node *cmp = cl->loopexit()->cmp_node();
  assert(cmp != NULL && cmp->req() == 3, "no loop limit found");

  // Node *limit = cmp->in(LIMIT);

  // Node *new_stride = ConNode::make(TypeInt::make(vlen));
  // Node *adjusted_limit = new SubINode(limit, new_stride);

  // assert(adjusted_limit != NULL, "adj limit");

  // phase->igvn().register_new_node_with_optimizer(new_stride);
  // phase->igvn().register_new_node_with_optimizer(adjusted_limit);

  phase->igvn().replace_input_of(cmp, LIMIT, adjusted_limit);
}

bool build_stuff(Compile *C, IdealLoopTree *lpt, PhaseIdealLoop *phase, PhaseIterGVN *igvn, CountedLoopNode *cl) {
  const juint VLEN = 8;
  Node *induction_phi = cl->phi();
  if (induction_phi == NULL) return false;
  TRACE(MinCond, {
      tty->print_cr("Found induction phi N%d", induction_phi->_idx);
    });

  // PhiNode holding the current value of the recurrence variable.
  PhiNode *reduction_phi = find_recurrence_phi(cl);
  if (reduction_phi == NULL) return false;
  TRACE(MinCond, {
    tty->print_cr("Found reduction phi N%d", reduction_phi->_idx);
  });

  // Right hand side of the assignment.
  Node *rhs = find_rhs(reduction_phi); //find_rhs(acc_add, reduction_phi);
  if (rhs == NULL || rhs->req() < 2) return false;
  TRACE(MinCond, {
      tty->print_cr("Found right-hand-side N%d", rhs->_idx);
    });

  ResourceMark rm;

  ConMul con_mul;
  //ArrayLoadPattern *array_read = match_array_read(rhs->in(2), induction_phi);
  if (!match_con_mul(rhs->in(1), reduction_phi, con_mul)) {
    TRACE(Match, {
        tty->print_cr("Unable to find recurrence phi");
        tty->print("  "); rhs->dump(" right hand side");
      });

    return false;
  }

  PatternInstance *pi = match(rhs->in(2), induction_phi);
  if (pi == NULL) return false;

  // Build post-loop for the remaining iterations that does not fill
  // up a full vector.
  // Node *one = ConINode::make(1);
  // Node *post_init_trip = new AddINode(cl->phi(), one);
  // phase->igvn().register_new_node_with_optimizer(one);
  // phase->igvn().register_new_node_with_optimizer(post_init_trip);

  // NOTE: Post loop
  // CountedLoopNode* post_head;
  // {
  //   Node_List old_new;
  //   phase->insert_post_loop(lpt, old_new, cl, cl->loopexit(), cl->incr(),
  //                           cl->limit(), post_head);
  // }
  // post_head->loopexit()->_prob = 1.0f / (VLEN - 1);

  // Adjust main loop stride and limit.
  Node *new_limit = split_loop(lpt, phase, cl, VLEN);
  set_stride(cl, phase, VLEN);
  adjust_limit(cl, phase, new_limit);

  // first_aligned_element(, int target_alignment)

  const uint VECTOR_BYTE_SIZE = VLEN * 4; // 4 4byte ints
  if (C->max_vector_size() < VECTOR_BYTE_SIZE) {
    C->set_max_vector_size(VECTOR_BYTE_SIZE);
  }

  // Node *out_phi = cl->find(155);
  // assert(out_phi->isa_Phi(), "a phi");

  // Constant multiplier
  Node *mulv = make_vector(phase, my_pow(con_mul.multiplier, VLEN), VLEN);

  Node *arr = pi->generate(phase, VLEN); //build_array_load(phase, array_read, VLEN);

  Node *initial_acc = new PromoteINode(reduction_phi->in(1), TypeVect::make(T_INT, VLEN)); // make_vector(phase, 0, VLEN);
  phase->igvn().register_new_node_with_optimizer(initial_acc);
  Node *m = make_exp_vector(phase, con_mul.multiplier, VLEN);

  // NOTE: WAS reduction_phi->in(PhiNode::Region)
  Node *phi = PhiNode::make(induction_phi->in(PhiNode::Region), initial_acc);
  phase->igvn().register_new_node_with_optimizer(phi);

  // TODO: Investigate performance if replaced with vector x scalar
  // multiplication (`mulv` is a vector of scalar duplicates).
  Node *mul0;

  // If we do not multiply our recurrence variable, don't create an
  // multiplication.
  if (con_mul.multiplier != 1) {
    mul0 = new MulVINode(mulv, phi, TypeVect::make(T_INT, VLEN));
    phase->igvn().register_new_node_with_optimizer(mul0);
  } else {
     mul0 = phi;
  }

  Node *mul1 = new MulVINode(arr, m, TypeVect::make(T_INT, VLEN));
  phase->igvn().register_new_node_with_optimizer(mul1);

  Node *add = new AddVINode(mul0, mul1, TypeVect::make(T_INT, VLEN));
  phase->igvn().register_new_node_with_optimizer(add);

  phi->set_req(2, add);

  // TODO: Replace with initial reduction phi value:
  ConNode *reduce_base = ConNode::make(TypeInt::make(0));
  Node *reduce = ReductionNode::make(Op_AddI, NULL, reduce_base, add, T_INT);

  phase->igvn().register_new_node_with_optimizer(reduce_base, NULL);
  phase->igvn().register_new_node_with_optimizer(reduce, NULL);

  // Node *opq = new Opaque1Node(C, reduction_phi->in(1));
  // phase->igvn().register_new_node_with_optimizer(opq);

  // Node *final_add = new AddINode(reduce, opq);
  // phase->igvn().register_new_node_with_optimizer(final_add);


  phase->igvn().replace_node(rhs, reduce); // Replace right hand side with reduction.
  // phase->igvn().replace_input_of(acc_add, 2, reduce);

  int n_unrolls = exact_log2(VLEN);
  while (n_unrolls--) {
    cl->double_unrolled_count();
  }

  //lpt->loop_predication(phase);
  // phase->update_main_loop_skeleton_predicates(cl->skip_strip_mined()->in(LoopNode::EntryControl),
  //                                             cl, cl->init_trip(),
  //                                             8);

  // cl->double_unrolled_count();
  // cl->double_unrolled_count();

  //cl->set_slp_max_unroll(VEC_SIZE);

  return true;
  // tty->print("Patternmatching *32: %d\n", match_con_mul(rhs->in(1), reduction_phi, con_mul));
  // tty->print("Patternmatching a[i]: %d\n", match_array_read(rhs->in(2), reduction_phi, array_read));

  // tty->print("CL %d: reduction_phi=%d, acc_add=%d, rhs=%d, rhs[1] is mul31*phi=%d\n",
  //           cl->_idx,
  //           reduction_phi->_idx,
  //           acc_add->_idx,
  //           rhs->_idx,
  //           is_x_mul_31(rhs->in(1), reduction_phi));
}

bool polynomial_reduction_analyze(Compile* C, PhaseIdealLoop *phase, PhaseIterGVN *igvn, IdealLoopTree *lpt) {
  if (!SuperWordPolynomial) return false;
  if (!lpt->is_counted() || !lpt->is_innermost()) return false;
  CountedLoopNode *cl = lpt->_head->as_CountedLoop();
  if (cl->has_passed_idiom_analysis() || cl->is_vectorized_loop() ||
      !cl->is_normal_loop()) return false;

  TRACE(Candidates, {
      tty->print_cr("Initial analysis of %s::%s",
                    C->method()->get_Method()->klass_name()->as_utf8(),
                    C->method()->get_Method()->name()->as_utf8());
    });

  if (!cl->stride_is_con()) return false;
  TRACE(Candidates, {
      tty->print_cr("  Loop is constant stride");
    });

  // NOTE: Do we need/want this one?
  if (cl->range_checks_present()) return false;

  TRACE(Candidates, {
      tty->print_cr("  Loop has no range checks");
      tty->print_cr("  ALL OK!");
    });

  C->print_method(PHASE_BEFORE_IDIOM_VECTORIZATION);

  TRACE(Match, {
      tty->print_cr("Starting analysis of %s::%s",
                    C->method()->get_Method()->klass_name()->as_utf8(),
                    C->method()->get_Method()->name()->as_utf8());
    });

  bool ok = build_stuff(C, lpt, phase, igvn, cl);
  cl->mark_was_idiom_analyzed();
  if (ok) {
    TRACE(Success, {
        tty->print_cr("Transformed %s::%s",
                      C->method()->get_Method()->klass_name()->as_utf8(),
                      C->method()->get_Method()->name()->as_utf8());
        // C->method()->get_Method()->set_dont_inline(true);
      });

    cl->mark_passed_idiom_analysis();
    cl->mark_loop_vectorized();
    C->print_method(PHASE_AFTER_IDIOM_VECTORIZATION);
    return true;
  } else {
    TRACE(Failure, {
        tty->print_cr("Failed %s::%s",
                      C->method()->get_Method()->klass_name()->as_utf8(),
                      C->method()->get_Method()->name()->as_utf8());
      });
    C->print_method(PHASE_FAILED_IDIOM_VECTORIZATION);
  }

  return false;
}

#undef TRACE
#undef ANY
