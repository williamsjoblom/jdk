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
#include "opto/castnode.hpp"
#include "opto/convertnode.hpp"

/****************************************************************
 * Forward declarations.
 ***************************************************************/
Node *make_vector(PhaseIdealLoop *phase, Node *init, const Type *recurr_t,
                  juint vec_size, Node *control=NULL);
Node *make_vector(PhaseIdealLoop *phase, jlong init, const Type *recurr_t,
                  juint vec_size, Node *control=NULL);
void adjust_limit(CountedLoopNode *cl, PhaseIterGVN &igvn, Node *adjusted_limit);
template<typename T>
T my_pow(T n, jint exp);

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

// Enabled trace options.
const int TRACE_OPTS = NoTraceOpts;

// Maximum search depth for `find_node`.
//
// TODO: The current value of `20` is most likely too high and is
// likely to produce a significant compile-time performance hit.
// NOTE: Currently unused, no fix needed.
const uint MAX_SEARCH_DEPTH = 20;

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

bool is_primitive_store(Node *n) {
  // FIXME: Verify that the store is primitive.
  return n->is_Store();
}

bool is_mul(Node *n) { return n->is_Mul(); }
bool is_add(Node *n) { return n->is_Add(); }
bool is_sub(Node *n) { return n->is_Sub(); }
bool is_lshift(Node *n) { return n->Opcode() == Op_LShiftI || n->Opcode() == Op_LShiftL; }

// Is integer valued binop?
bool is_binop_i(Node *n) {
  int opc = n->Opcode();
  return
    opc == Op_AddI ||
    opc == Op_SubI ||
    opc == Op_MulI ||
    opc == Op_DivI ||
    opc == Op_LShiftI;
}

// Is long valued binop?
bool is_binop_l(Node *n) {
  int opc = n->Opcode();
  return
    opc == Op_AddL ||
    opc == Op_SubL ||
    opc == Op_MulL ||
    opc == Op_DivL ||
    opc == Op_LShiftL;
}

// Is float valued binop?
bool is_binop_f(Node *n) {
  int opc = n->Opcode();
  return
    opc == Op_AddF ||
    opc == Op_SubF ||
    opc == Op_MulF ||
    opc == Op_DivF;
}

// Is double valued binop?
bool is_binop_d(Node *n) {
  int opc = n->Opcode();
  return
    opc == Op_AddD ||
    opc == Op_SubD ||
    opc == Op_MulD ||
    opc == Op_DivD;
}

bool is_binop(Node *n) {
  return
    is_binop_i(n) || is_binop_l(n) ||
    is_binop_f(n) || is_binop_d(n);
}

/****************************************************************
 * Minimum matching condition.
 ****************************************************************/
bool has_control_flow(CountedLoopNode *cl) {
  // TODO: Bad negation?
  Node *exit = cl->loopexit();
  return exit->in(0) == cl;
}

PhiNode *find_recurrence_phi(CountedLoopNode *cl, bool memory=false) {
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
    bool memory_reduction = memory &&
      n->bottom_type()->base() == Type::Memory;
    bool primitive_reduction = !memory &&
      is_java_primitive(n->bottom_type()->basic_type());

    if (n->is_Phi() && n != induction_phi &&
        (primitive_reduction || memory_reduction)) {
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

  // Node_List inputs;
  // for (uint i = PhiNode::Input; i < reduction_phi->len(); i++) {
  //   inputs.push(reduction_phi->in(i));
  // }

  // Unique_Node_List visited;
  // Node *bottom = find_nodes(reduction_phi, inputs, visited);

  // return bottom;
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
              next != NULL ? next->dump("  found\n") : tty->print_cr("  NULL found");
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
  virtual Node *generate(PhaseIdealLoop *phase, const Type *recurr_t, uint vlen) = 0;
  virtual Node *result() = 0;

  virtual bool has_alignable_load() = 0;
  virtual int memory_stride() { return 0; }
  virtual BasicType elem_bt() { ShouldNotCallThis(); return T_ILLEGAL; }
  virtual Node *base_addr() = 0;
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

  // Index offset.
  Node *_offset;

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

  virtual Node *generate(PhaseIdealLoop *phase, const Type *recurr_t, uint vlen) {
    assert(_offset == NULL, "not implemented");
    BasicType recurr_bt = recurr_t->array_element_basic_type();

    LoadNode *load = _load->as_Load();
    BasicType load_type = _bt;
    BasicType elem_type = load->memory_type();

    TRACE(Rewrite, {
        tty->print_cr("load: %s, elem: %s, recur: %s", type2name(load_type),
                      type2name(elem_type), type2name(recurr_bt));
      });

    // No implicit cast.
    if (elem_type == recurr_bt) {
      Node *arr = LoadVectorNode::make(
        _load->Opcode(), _load->in(LoadNode::Control),
        _memory, _load->in(LoadNode::Address),
        _load->adr_type(), vlen, recurr_bt);
      phase->igvn().register_new_node_with_optimizer(arr, NULL);
      return arr;
    } else {
      Node *arr = LoadVectorNode::make_promotion(
        _load->Opcode(), _load->in(LoadNode::Control),
        _memory, _load->in(LoadNode::Address),
        _load->adr_type(), vlen, recurr_bt);
      phase->igvn().register_new_node_with_optimizer(arr, NULL);
      return arr;
    }

    ShouldNotReachHere();
    return NULL;
  }

  virtual Node *result() { return _load; }

  virtual bool has_alignable_load() { return true; }
  virtual int memory_stride() { return _elem_byte_size; }
  virtual BasicType elem_bt() { return _load->as_Load()->memory_type(); }
  virtual Node *base_addr() { return _array_ptr; }
};

struct ScalarPattern : PatternInstance {
  Node *_scalar;

  virtual Node *generate(PhaseIdealLoop *phase, const Type *recurr_t, uint vlen) {
    return make_vector(phase, _scalar, recurr_t, vlen);
  }

  virtual Node *result() {
    return _scalar;
  }

  virtual bool has_alignable_load() { return false; }
  virtual Node *base_addr() { ShouldNotCallThis(); return NULL; }
};

struct BinOpPattern : PatternInstance {
  int _opcode;
  PatternInstance *_lhs, *_rhs;
  BasicType _bt;

  virtual Node *generate(PhaseIdealLoop *phase, const Type *recurr_t, uint vlen) {
    Node *lhs = _lhs->generate(phase, recurr_t, vlen);
    Node *rhs = _rhs->generate(phase, recurr_t, vlen);

    // TODO: Should we use `_bt` or `recurr_t->array_element_basic_type()` here?
    Node *result = VectorNode::make(_opcode, lhs, rhs, vlen, _bt);
    phase->igvn().register_new_node_with_optimizer(result);
    return result;
  }

  virtual Node *result() {
    ShouldNotCallThis();
    return NULL;
  }

  virtual bool has_alignable_load() {
    return
      _lhs->has_alignable_load() ||
      _rhs->has_alignable_load();
  }

  virtual BasicType elem_bt() {
    if (_lhs->has_alignable_load()) return _lhs->elem_bt();
    else return _rhs->elem_bt();
  }

  virtual Node *base_addr() {
    if (_lhs->has_alignable_load()) return _lhs->base_addr();
    else return _rhs->base_addr();
  }
};

struct LShiftPattern : BinOpPattern {
  virtual Node *generate(PhaseIdealLoop *phase, const Type *recurr_t, uint vlen) {
    assert(_opcode == Op_LShiftI, "sanity");
    assert(_rhs->result()->is_Con(), "not implemented");

    BasicType recurr_bt = recurr_t->array_element_basic_type();
    Node *lhs = _lhs->generate(phase, recurr_t, vlen);

    Node *multiplier = phase->igvn().intcon(1 << _rhs->result()->get_int());
    // TODO: `make_vector` needs control dependency on loop entry
    // control, without this dependency the vector initialization may
    // be scheduled before the deciding on vector/scalar loop.
    Node *result = VectorNode::make(Op_MulI, lhs, make_vector(phase, multiplier, recurr_t, vlen), vlen, recurr_bt);
    //new MulVINode(lhs, make_vector(phase, multiplier, vlen),
    //TypeVect::make(recurr_bt, vlen));
    phase->igvn().register_new_node_with_optimizer(result);
    return result;
  }
};

struct ConMul {
  JavaValue multiplier;
};

enum NFactorInfo {
  NOT_FOUND = 0,
  IDENTITY = 1,
  NOT_IDENTITY = 2,
};

void assign_identity(JavaValue& value, BasicType bt) {
  switch (bt) {
  case T_BOOLEAN:
  case T_BYTE:
  case T_CHAR:
  case T_SHORT:
  case T_INT:
    value.set_jint(1);
    break;
  case T_LONG:
    value.set_jlong(1);
    break;
  case T_FLOAT:
    value.set_jfloat(1);
    break;
  case T_DOUBLE:
    value.set_jdouble(1);
    break;
  default:
    ShouldNotReachHere();
    break;
  }
}

// Match `of` multiplied by a constant that has been rewritten as a
// shift and an add/sub.
NFactorInfo match_shift_con_mul(Node *start, Node *of, JavaValue &result) {
  enum {
    SHIFT_DISTANCE,
    SUB,
    ADD,
    N_REFS
  };

  ResourceMark rm;
  Pattern *l_shift = new Pred2Pattern<3>
    (is_lshift,
     ANY,
     new ExactNodePattern(of),
     new OpcodePattern<0>(Op_ConI, SHIFT_DISTANCE));

  Pattern *shift_sub = new Pred2Pattern<3>
    (is_sub,
     ANY,
     l_shift,
     new ExactNodePattern(of),
     SUB);

  Pattern *shift_add = new Pred2Pattern<3>
    (is_add,
     ANY,
     l_shift,
     new ExactNodePattern(of),
     ADD);

  Pattern *shift = new OrPattern(shift_sub, new OrPattern(shift_add, l_shift));

  MatchRefs refs(N_REFS);
  if (shift->match(start, refs)) {
    jlong multiplier = (1 << refs[SHIFT_DISTANCE]->get_int());
    if (refs[SUB]) {
      multiplier--;
    } else if (refs[ADD]) {
      multiplier++;
    }

    result = JavaValue(multiplier);
    return NOT_IDENTITY; //ConNode::make(TypeInt::make(multiplier));
  } else {
    TRACE(Match, {
        tty->print_cr("  origin shift_con_mul");
      });
    return NOT_FOUND;
  }
}

NFactorInfo match_trivial_con_mul(Node *start, Node *of, JavaValue &result) {
  enum {
    MUL,
    N_REFS
  };

  MatchRefs refs(N_REFS);
  Pattern *int_mul = new OpcodePattern<3>
    (Op_MulI,
     ANY,
     new ExactNodePattern(of),
     new OpcodePattern<0>(Op_ConI, MUL));

  if (int_mul->match(start, refs)) {
    result = refs[MUL]->get_int();
    return NOT_IDENTITY;
  }

  Pattern *float_mul = new OpcodePattern<3>
    (Op_MulF,
     ANY,
     new ExactNodePattern(of),
     new OpcodePattern<0>(Op_ConF, MUL));

  if (float_mul->match(start, refs)) {
    result = JavaValue(refs[MUL]->getf());
    return NOT_IDENTITY;
  }

  Pattern *double_mul = new OpcodePattern<3>
    (Op_MulD,
     ANY,
     new ExactNodePattern(of),
     new OpcodePattern<0>(Op_ConD, MUL));

  if (double_mul->match(start, refs)) {
    result = JavaValue(refs[MUL]->getd());
    return NOT_IDENTITY;
  }

  return NOT_FOUND;
}

NFactorInfo match_identity_con_mul(Node *start, Node *of, BasicType recurr_bt, JavaValue &result) {
  if (start == of) {
    assign_identity(result, recurr_bt);
    return IDENTITY;
  } else {
    TRACE(Match, {
        tty->print_cr("  origin identity_con_mul");
      });
    return NOT_FOUND;
  }
}

// Match multiplication of `of` and a constant placing the constant in
// `result`.
NFactorInfo find_n_factor(Node *start, Node *of, BasicType recurr_bt, JavaValue &result) {
  if (NFactorInfo r = match_identity_con_mul(start, of, recurr_bt, result))
    return r;
  if (NFactorInfo r = match_shift_con_mul(start, of, result))
    return r;
  if (NFactorInfo r = match_trivial_con_mul(start, of, result))
    return r;

  return NOT_FOUND;
}

// Strip eventual conversions, returning the node being converted and
// setting `bt` to the resulting type of the conversion.
Node *strip_conversions(Node *start, BasicType& bt) {
  if (is_binop_f(start)) {
    bt = T_FLOAT;
    return start;
  }
  if (is_binop_d(start)) {
    bt = T_DOUBLE;
    return start;
  }

  // LShift followed by RShift for narrowing of ints.
  if (start->Opcode() == Op_RShiftI &&
      start->in(1)->Opcode() == Op_LShiftI &&
      start->in(2)->Opcode() == Op_ConI &&
      start->in(1)->in(2) == start->in(2)) {
    Node *con = start->in(2);
    switch (con->get_int()) {
    case 16: bt = T_SHORT; break;
    case 24: bt = T_BYTE; break;
    default: ShouldNotReachHere();
    }

    return start->in(1)->in(1);
  } else {
    bt = T_INT;
    return start;
  }
}

ArrayLoadPattern *match_array_access(Node *start, Node *idx,
                                     NodePred start_predicate,
                                     bool allow_offset=false) {
  ArrayLoadPattern *result = new ArrayLoadPattern();

  ResourceMark rm;

  enum {
    LOAD_NODE,
    LOAD_CTRL,
    ARRAY,
    MEMORY,
    IDX_SHIFT_DISTANCE,
    IDX_OFFSET,
    ARRAY_BASE_OFFSET,
    CAST_II,

    N_REFS
  };

  MatchRefs refs(N_REFS);


  Pattern *exact_idx = new ExactNodePattern(idx);

  // FIXME: unnessecary initialization if allow_offset is false.
  Pattern *idx_offset = new OpcodePattern<3>
    (Op_AddI,
     ANY,
     exact_idx,
     new CapturePattern(IDX_OFFSET));

  Pattern *idx_pattern = allow_offset
    ? new OrPattern(idx_offset, exact_idx)
    : exact_idx;

  Pattern *pre_shift = new OpcodePattern<2> // LShiftL: Left-hand side
    (Op_ConvI2L,
     ANY,                          // ConvI2L: Control
     new OpcodePattern<2> // ConvI2L: Data
     (Op_CastII,
      ANY,                         // CastII:  Control
      idx_pattern,   // CastII:  Index
      CAST_II));

  Pattern *shift = new OpcodePattern<3>  // AddP: Offset
    (Op_LShiftL,
     ANY,                           // LShiftL: Control
     pre_shift,
     new OpcodePattern<0>(Op_ConI, IDX_SHIFT_DISTANCE));

  Pattern *p = new Pred2Pattern<3>
    (start_predicate, // Match load nodes of primitive type.
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


  // NOTE: If we start at a ConvI2L, skip that node and force _bt to
  // T_LONG.
  bool is_long = false;
  if (start->Opcode() == Op_ConvI2L) {
    is_long = true;
    start = start->in(1);
  }

  if (p->match(start, refs)) {
    result->_load_ctrl = refs[LOAD_CTRL];
    result->_load = refs[LOAD_NODE];
    result->_bt = is_long ? T_LONG : result->_load->bottom_type()->basic_type();
    result->_index = idx;
    result->_offset = refs[IDX_OFFSET];
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

ArrayLoadPattern *match_array_read(Node *start, Node *idx,
                                   bool allow_offset = false) {
  return match_array_access(start, idx, is_primitive_load, allow_offset);
}

ArrayLoadPattern *match_array_store(Node *start, Node *idx,
                                    bool allow_offset = false) {
  return match_array_access(start, idx, is_primitive_store, allow_offset);
}

// // Match array read.
// ArrayLoadPattern *match_array_read(Node *start, Node *idx,
//                                    bool allow_offset=false) {
//   ArrayLoadPattern *result = new ArrayLoadPattern();

//   ResourceMark rm;

//   enum {
//     LOAD_NODE,
//     LOAD_CTRL,
//     ARRAY,
//     MEMORY,
//     IDX_SHIFT_DISTANCE,
//     IDX_OFFSET,
//     ARRAY_BASE_OFFSET,
//     CAST_II,

//     N_REFS
//   };

//   MatchRefs refs(N_REFS);


//   Pattern *exact_idx = new ExactNodePattern(idx);

//   // FIXME: unnessecary initialization if allow_offset is false.
//   Pattern *idx_offset = new OpcodePattern<3>
//     (Op_AddI,
//      ANY,
//      exact_idx,
//      new CapturePattern(IDX_OFFSET));

//   Pattern *idx_pattern = allow_offset
//     ? new OrPattern(idx_offset, exact_idx)
//     : exact_idx;

//   Pattern *pre_shift = new OpcodePattern<2> // LShiftL: Left-hand side
//     (Op_ConvI2L,
//      ANY,                          // ConvI2L: Control
//      new OpcodePattern<2> // ConvI2L: Data
//      (Op_CastII,
//       ANY,                         // CastII:  Control
//       idx_pattern,   // CastII:  Index
//       CAST_II));

//   Pattern *shift = new OpcodePattern<3>  // AddP: Offset
//     (Op_LShiftL,
//      ANY,                           // LShiftL: Control
//      pre_shift,
//      new OpcodePattern<0>(Op_ConI, IDX_SHIFT_DISTANCE));

//   Pattern *p = new Pred2Pattern<3>
//     (is_primitive_load, // Match load nodes of primitive type.
//      new CapturePattern(LOAD_CTRL),
//      new CapturePattern(MEMORY),
//      new OpcodePattern<4>
//      (Op_AddP,
//       ANY,
//       ANY,
//       new OpcodePattern<4>
//       (Op_AddP,
//        ANY,                            // AddP: Control
//        ANY,                            // AddP: Base
//        new PredPattern(is_array_ptr, ARRAY), // AddP: Address
//        new OrPattern(shift, pre_shift)),
//       new OpcodePattern<0>(Op_ConL, ARRAY_BASE_OFFSET)),
//       LOAD_NODE);


//   // NOTE: If we start at a ConvI2L, skip that node and force _bt to
//   // T_LONG.
//   bool is_long = false;
//   if (start->Opcode() == Op_ConvI2L) {
//     is_long = true;
//     start = start->in(1);
//   }

//   if (p->match(start, refs)) {
//     result->_load_ctrl = refs[LOAD_CTRL];
//     result->_load = refs[LOAD_NODE];
//     result->_bt = is_long ? T_LONG : result->_load->bottom_type()->basic_type();
//     result->_index = idx;
//     result->_offset = refs[IDX_OFFSET];
//     result->_result = start;
//     result->_array_ptr = refs[ARRAY];
//     result->_memory = refs[MEMORY];
//     result->_elem_byte_size =
//       1 << (refs[IDX_SHIFT_DISTANCE] != NULL
//             ? refs[IDX_SHIFT_DISTANCE]->get_int()
//             : 0);
//     result->_base_offset = refs[ARRAY_BASE_OFFSET]->get_long();

//     assert(result->_load_ctrl->isa_Proj(), "");
//     return result;
//   } else {
//     TRACE(Match, {
//         tty->print_cr("  origin array_read");
//       });
//     return NULL;
//   }
// }



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
  if (start->Opcode() == Op_ConI || start->Opcode() == Op_ConF) {
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

  // // NOTE: Ignore conversions for now. Since we already know the type
  // // of the recurrence variable these conversions are embedded within
  // // our vector loads.
  // if (start->Opcode() == Op_ConvI2L) {
  //   assert(start->in(0) == NULL, "conversion has control");
  //   return match(start->in(1), iv);
  // }

  TRACE(Match, {
      tty->print_cr("Unable to find pattern instance.");
      tty->print("  "); start->dump(" start node");
    });

  return NULL;
}

/****************************************************************
 * Pattern instance alignment.
 ****************************************************************/

struct AlignInfo {
  Node *_base_addr;
  BasicType _elem_bt;
};

// Number of iterations that are to be taken to satisfy alignment constraints.
// Constant folded down to a `&`, `-`, and `<<`.
Node *pre_loop_align_limit(PhaseIterGVN &igvn, Node *target_align,
                           Node *ptr_first_elem, int elem_size) {
  // ptr_first_elem % target_align (assumes `target_align` to be power of 2).
  Node *target_minus1 = igvn.transform(new AddINode(target_align, igvn.intcon(-1)));
  Node *mod = igvn.transform(new AndINode(ptr_first_elem, target_minus1));

  // target_align - ptr_first_elem%target_align
  Node *sub = igvn.transform(new SubINode(target_align, mod));
  // (target_align - ptr_first_elem%target_align) / elem_size
  Node *div = igvn.transform(new URShiftINode(sub, igvn.intcon(log2_int(elem_size))));
  return div;
}

void align_first_main_loop_iters(PhaseIterGVN &igvn, CountedLoopNode *pre_loop, Node *orig_limit,
                                AlignInfo align, int vlen) {
  Node *base = align._base_addr;
  Node *base_offset = igvn.intcon(arrayOopDesc::base_offset_in_bytes(align._elem_bt));
  Node *first_elem_ptr = igvn.transform(new AddPNode(base, base, base_offset));
  Node *x_elem_ptr = igvn.transform(new CastP2XNode(NULL, first_elem_ptr));
#ifdef _LP64
  // Cast long pointer to integer in case of 64 bit architecture.
  // Since alignment is determined by the last few bits, we only
  // need the least significant part of the pointer anyways.
  x_elem_ptr = new ConvL2INode(x_elem_ptr);
  igvn.register_new_node_with_optimizer(x_elem_ptr);
#endif
  uint target_align = type2aelembytes(align._elem_bt)*vlen;
  Node *target_align_con = igvn.intcon(target_align);

  Node *new_limit = pre_loop_align_limit(igvn, target_align_con, x_elem_ptr,
                                         type2aelembytes(align._elem_bt));
  Node *constrained_limit = new MinINode(orig_limit, new_limit);
  igvn.register_new_node_with_optimizer(constrained_limit);

  adjust_limit(pre_loop, igvn, constrained_limit);
}

/****************************************************************
 * Utility.
 ****************************************************************/
int mul_opcode(BasicType bt) {
  switch (bt) {
  case T_BOOLEAN:
  case T_BYTE:
  case T_CHAR:
  case T_SHORT:
  case T_INT:
    return Op_MulI;
  case T_FLOAT:
    return Op_MulF;
  case T_DOUBLE:
    return Op_MulD;
  default:
    ShouldNotReachHere();
    return 0;
  }
}

int add_opcode(BasicType bt) {
  switch (bt) {
  case T_BOOLEAN:
  case T_BYTE:
  case T_CHAR:
  case T_SHORT:
  case T_INT:
    return Op_AddI;
  case T_FLOAT:
    return Op_AddF;
  case T_DOUBLE:
    return Op_AddD;
  default:
    ShouldNotReachHere();
    return 0;
  }
}

// Is the given operator associative?
bool is_associative(int opc) {
  switch (opc) {
  case Op_AddI:
  case Op_OrI:
  case Op_XorI:
  case Op_MaxI:
  case Op_MinI:
  case Op_AddL:
  case Op_OrL:
  case Op_XorL:
  case Op_AddF:
  case Op_MaxF:
  case Op_MinF:
  case Op_AddD:
  case Op_MaxD:
  case Op_MinD:
  case Op_MulI:
  case Op_MulL:
  case Op_MulF:
  case Op_MulD:
    return true;
  default:
    return false;
  }
}

// Return a constant holding the identity of the given scalar opcode.
Node *identity_con(int opc) {
  assert(is_associative(opc), "expected");
  switch (opc) {
  // Additive identity (0):
  case Op_AddI:
  case Op_OrI:
  case Op_XorI:
  case Op_MaxI:
  case Op_MinI:
    return ConNode::make(TypeInt::make(0));
  case Op_AddL:
  case Op_OrL:
  case Op_XorL:
    return ConNode::make(TypeLong::make(0));
  case Op_AddF:
  case Op_MaxF:
  case Op_MinF:
    return ConNode::make(TypeF::make(0));
  case Op_AddD:
  case Op_MaxD:
  case Op_MinD:
    return ConNode::make(TypeD::make(0));

  // Multiplicative identity (1):
  case Op_MulI:
    return ConNode::make(TypeInt::make(1));
  case Op_MulL:
    return ConNode::make(TypeLong::make(1));
  case Op_MulF:
    return ConNode::make(TypeF::make(1));
  case Op_MulD:
    return ConNode::make(TypeD::make(1));
  default:
    // TODO: Reaches here in Tools-Javadoc-Startup
    ShouldNotReachHere();
    return NULL;
  }
}

// n^exp
template<typename T>
T my_pow(T n, jint exp) {
  T result = 1;
  while (exp--) {
    result *= n;
  }
  return result;
}

JavaValue make_pow(JavaValue n, jint exp, BasicType bt) {
  switch (bt) {
  case T_BYTE:
  case T_BOOLEAN:
  case T_CHAR:
  case T_SHORT:
  case T_INT:
    return JavaValue(my_pow<jint>(n.get_jint(), exp));
  case T_LONG:
    return JavaValue(my_pow<jlong>(n.get_jlong(), exp));
  case T_FLOAT:
    return JavaValue(my_pow<jfloat>(n.get_jfloat(), exp));
  case T_DOUBLE:
    return JavaValue(my_pow<jdouble>(n.get_jdouble(), exp));
  default:
    ShouldNotReachHere();
    return 0;
  }
}


// Make int vector containing [init, init, ..., init]
Node *make_vector(PhaseIdealLoop *phase, Node *init, const Type *recurr_t, juint vec_size,
                  Node *control) {
  Node *v = VectorNode::scalar2vector(init, vec_size, recurr_t);
  if (control != NULL) v->init_req(0, control);
  return phase->igvn().transform(v);
}

// Make int vector containing [init, init, ..., init]
Node *make_vector(PhaseIdealLoop *phase, JavaValue init, const Type *recurr_t, juint vec_size,
                  Node *control) {
  Node *init_con;
  switch (recurr_t->basic_type()) {
  case T_BYTE:
  case T_SHORT:
  case T_CHAR:
  case T_INT:
    init_con = phase->igvn().transform(ConNode::make(TypeInt::make(init.get_jint())));
    break;
  case T_LONG:
    init_con = phase->igvn().transform(ConNode::make(TypeLong::make(init.get_jlong())));
    break;
  case T_FLOAT:
    init_con = phase->igvn().transform(ConNode::make(TypeF::make(init.get_jfloat())));
    break;
  case T_DOUBLE:
    init_con = phase->igvn().transform(ConNode::make(TypeD::make(init.get_jdouble())));
    break;
  default:
    ShouldNotReachHere();
  }

  return make_vector(phase, init_con, recurr_t, vec_size, control);
}

template<typename T>
jlong exp_vector_part(int i, T n, int elem_bytes) {
  uint64_t mask = (1l << elem_bytes*8) - 1;

  jlong result = 0;
  T next_n = my_pow<T>(n, i * (sizeof(jlong) / elem_bytes));
  for (uint i = 0; i < sizeof(jlong) / elem_bytes; i++) {
    jlong next_l = 0; memcpy(&next_l, &next_n, sizeof(next_n));
    result = (next_l & mask) | (result << (elem_bytes*8));
    next_n *= n;
  }
  return result;
}

jlong make_exp_vector_part(int i, JavaValue n, int elem_bytes, BasicType bt) {
  switch (bt) {
  case T_BYTE:
  case T_BOOLEAN:
  case T_CHAR:
  case T_SHORT:
  case T_INT:
    return exp_vector_part(i, n.get_jint(), elem_bytes);
  case T_LONG:
    return exp_vector_part(i, n.get_jlong(), elem_bytes);
  case T_FLOAT:
    return exp_vector_part(i, n.get_jfloat(), elem_bytes);
  case T_DOUBLE:
    return exp_vector_part(i, n.get_jdouble(), elem_bytes);
  default:
    ShouldNotReachHere();
    return 0;
  }
}

// Make vector containing [n^{vlen}, n^{vlen-1}, ..., n^1, n^0].
Node *make_exp_vector(PhaseIdealLoop *phase, JavaValue n, juint vlen, const Type *t,
                      Node *control) {
  // if (0 <= n && n <= 1) {
  //   // [0^3, 0^2, 0^1, 0^0] = [0, 0, 0, 0] and
  //   // [1^3, 1^2, 1^1, 1^0] = [1, 1, 1, 1]
  //   return make_vector(phase, n, t, vlen);
  // }

  BasicType bt = t->array_element_basic_type();
  int elem_bytes = type2aelembytes(bt);
  int elem_bits = elem_bytes*8;
  int vector_bytes = type2aelembytes(bt)*vlen;

  assert(vector_bytes == 16 || vector_bytes == 32, "expected");

  PhaseIterGVN& igvn = phase->igvn();

  // TODO: The following code need to be modified to support
  // big-endian systems, fixed by adjusting shift distances depending
  // on target endianness.
  if (vector_bytes == 16) {
    Node *a = igvn.transform(ConNode::make(TypeLong::make(make_exp_vector_part(0, n, elem_bytes, bt))));
    Node *b = igvn.transform(ConNode::make(TypeLong::make(make_exp_vector_part(1, n, elem_bytes, bt))));

    // tty->print_cr("Make 16 byte exponential vector: a-lo: 0x%x a-hi: 0x%x b-lo: 0x%x b-hi: 0x%x",
    //               static_cast<uint32_t>(a->get_long() & UINT32_MAX),
    //               static_cast<uint32_t>(static_cast<uint64_t>(a->get_long()) >> 32),
    //               static_cast<uint32_t>(b->get_long() & UINT32_MAX),
    //               static_cast<uint32_t>(static_cast<uint64_t>(b->get_long()) >> 32));

    Node *con = VectorNode::scalars2vector(a, b, bt);
    if (control) con->set_req(0, control);
    return igvn.transform(con);
  }

  if (vector_bytes == 32) {
    Node *a = igvn.transform(ConNode::make(TypeLong::make(make_exp_vector_part(0, n, elem_bytes, bt))));
    Node *b = igvn.transform(ConNode::make(TypeLong::make(make_exp_vector_part(1, n, elem_bytes, bt))));
    Node *c = igvn.transform(ConNode::make(TypeLong::make(make_exp_vector_part(2, n, elem_bytes, bt))));
    Node *d = igvn.transform(ConNode::make(TypeLong::make(make_exp_vector_part(3, n, elem_bytes, bt))));
    Node *con_lo = igvn.transform(VectorNode::scalars2vector(d, c, bt));
    Node *con_hi = igvn.transform(VectorNode::scalars2vector(b, a, bt));
    Node *con = VectorNode::scalars2vector(con_lo, con_hi, bt);
    if (control) con->set_req(0, control);

    return igvn.transform(con);
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
                 CountedLoopNode *cl, juint vlen, Node_List& old_new) {
  assert(cl->is_normal_loop(), "loop has already been split");
  phase->insert_pre_post_loops(lpt, old_new, false);

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
void adjust_limit(CountedLoopNode *cl, PhaseIterGVN &igvn, Node *adjusted_limit) {
  // WARNING: (limit - stride) may underflow.
  // TODO: See `loopTransform.cpp:do_unroll()` for how to patch this up correctly.
  const uint LIMIT = 2;
  Node *cmp = cl->loopexit()->cmp_node();
  assert(cmp != NULL && cmp->req() == 3, "no loop limit found");
  igvn.replace_input_of(cmp, LIMIT, adjusted_limit);
}

// TODO: move to Matcher::
bool check_cpu_features(uint vbytes, BasicType recurr_bt) {
  bool r = true;

  switch (vbytes) {
  case 16: r &= VM_Version::supports_sse4_2(); break;
  case 32: r &= VM_Version::supports_avx2(); break;
  case 64: r &= VM_Version::supports_evex(); break;
  default: return false;
  }

  switch (recurr_bt) {
  case T_BYTE:
  case T_SHORT:
    r &= (vbytes == 64) ? VM_Version::supports_avx512bw() : true;
    break;
  case T_INT:
    break;
  case T_LONG:
    r &= VM_Version::supports_avx512vldq();
    break;
  default:
    return false;
  }

  return r;
}

int prologue_cost() {
  // TODO
  return 0;
}

int epilogue_cost() {
  // TODO
  return 0;
}

// Return an estimation of the minumum number of trips that has to be
// taken for the vectorized loop to be profitable.
int min_profitable_trips() {
  // TODO
  return 0;
}

bool go_prefix_sum(IdealLoopTree *lpt, PhaseIdealLoop *phase, CountedLoopNode *cl, PhaseIterGVN &igvn,
                   Node *induction_phi, Node *reduction_phi) {
  // FIXME: Hardcoded constants for now...
  const Type *recurr_t = TypeInt::INT;
  const BasicType recurr_bt = T_INT;
  const int VLEN = 4;
  const int ELEM_SZ = type2aelembytes(recurr_bt);



  tty->print_cr("GO_PREFIX_SUM!");
  // induction_phi->dump(" i.v.\n");
  // reduction_phi->dump(" r.v.\n");

  Node *store = reduction_phi->in(2);
  if (!store->is_Store()) return false;
  Node *stored_value = store->in(3);
  if (!stored_value->is_Add()) return false;

  tty->print_cr("Passed first checks!");

  ArrayLoadPattern *store_inst = match_array_store(store, induction_phi, true);
  if (store_inst == NULL) return false;
  ArrayLoadPattern *lhs = match_array_read(stored_value->in(1), induction_phi, true);
  ArrayLoadPattern *rhs = match_array_read(stored_value->in(2), induction_phi, true);
  if (rhs == NULL || lhs == NULL) return false;

  tty->print_cr("Passed matching!");

  ArrayLoadPattern *prefix;
  ArrayLoadPattern *c;

  // One and only one offset of -1 required.
  if (lhs->_offset == NULL && rhs->_offset == NULL) {
    return false;
  } else if (lhs->_offset == NULL && rhs->_offset != NULL) {
    prefix = rhs;
    c = lhs;
  } else if (rhs->_offset == NULL && lhs->_offset != NULL) {
    prefix = lhs;
    c = rhs;
  } else {
    return false;
  }

  tty->print_cr("Passed initial offset check!");

  bool prefix_has_decremented_offset =
    prefix->_offset->is_Con() && prefix->_offset->get_int() == -1 &&
    store_inst->_offset == NULL;
  bool same_array = prefix->base_addr() == store_inst->base_addr();
  if (!prefix_has_decremented_offset || !same_array) return false;

  tty->print_cr("Passed offset/memory constraints!");

  Node_List old_new;
  Node *orig_limit = cl->limit();
  Node *new_limit = split_loop(lpt, phase, cl, VLEN, old_new);
  set_stride(cl, phase, VLEN);
  adjust_limit(cl, phase->igvn(), new_limit);

  Node *pre_stored_value = old_new[stored_value->_idx];

  Node *initial_prefix = VectorNode::scalar2vector(pre_stored_value, VLEN, recurr_t);
  igvn.register_new_node_with_optimizer(initial_prefix);
  Node *prefix_phi = PhiNode::make(induction_phi->in(PhiNode::Region), initial_prefix);
  igvn.register_new_node_with_optimizer(prefix_phi);

  Node *c_load = c->generate(phase, recurr_t, VLEN);
  Node *last_add = c_load;
  // Hillis and Steele parallel prefix sum algorithm:
  for (int i = 1; i < VLEN; i <<= 1) {
    Node *shift = new ElemLShiftVNode(last_add, igvn.intcon(ELEM_SZ*i),
                                      TypeVect::make(recurr_bt, VLEN));
    Node *add = VectorNode::make(Op_AddI, last_add, shift, VLEN, recurr_bt);
    igvn.register_new_node_with_optimizer(shift);
    igvn.register_new_node_with_optimizer(add);
    last_add = add;
  }


  // Node *shift1 = new ElemLShiftVNode(c_load, igvn.intcon(1*4), TypeVect::make(recurr_bt, VLEN));
  // Node *add1 = VectorNode::make(Op_AddI, c_load, shift1, VLEN, recurr_bt);
  // igvn.register_new_node_with_optimizer(shift1);
  // igvn.register_new_node_with_optimizer(add1);
  // Node *shift2 = new ElemLShiftVNode(add1, igvn.intcon(2*4), TypeVect::make(recurr_bt, VLEN));
  // Node *add2 = VectorNode::make(Op_AddI, add1, shift2, VLEN, recurr_bt);
  // igvn.register_new_node_with_optimizer(shift2);
  // igvn.register_new_node_with_optimizer(add2);

  Node *prev_prefix_add = VectorNode::make(Op_AddI, prefix_phi, last_add, VLEN, recurr_bt);
  igvn.register_new_node_with_optimizer(prev_prefix_add);

  Node *extract_last = new ExtractINode(prev_prefix_add, igvn.intcon(3));
  igvn.register_new_node_with_optimizer(extract_last);
  Node *repl_last = new ReplicateINode(extract_last, TypeVect::make(recurr_bt, VLEN));
  igvn.register_new_node_with_optimizer(repl_last);
  prefix_phi->set_req(2, repl_last);

  StoreVectorNode *storev = StoreVectorNode::make(store->Opcode(),
                                                  store->in(MemNode::Control),
                                                  store->in(MemNode::Memory),
                                                  store->in(MemNode::Address),
                                                  store->adr_type(), prev_prefix_add, VLEN);
  igvn.register_new_node_with_optimizer(storev);
  igvn.replace_node(store, storev);
  igvn.remove_dead_node(store);

  // We want to check that:
  //
  // - The prefix and c term shares memory state with the right hand
  // side of the assignment.
  //
  // - The prefix term shares the same address as the right hand side
  // - of the assignment (but decremented).

  tty->print_cr("Found prefix sum!");

  // prefix->_load->dump(" PREFIX\n");
  // c->_load->dump(" C_i\n");

  return true;
}

// Clone the loop to be vectorized, where the cloned, unvectorized,
// loop is picked for low tripcounts.
void build_loop_variants(PhaseIdealLoop *phase, IdealLoopTree *lpt,
                         CountedLoopNode *cl) {
  TRACE(Rewrite, {
      tty->print_cr("Start loop variants");
    });

  Node_List old_new;
  // Projection node for the vectorized loop.
  ProjNode *proj_true = phase->create_slow_version_of_loop(
    lpt, old_new, Op_If,
    PhaseIdealLoop::CloneIncludesStripMined);

  CountedLoopNode *slow_cl = old_new[cl->_idx]->as_CountedLoop();
  slow_cl->mark_was_idiom_analyzed();
  slow_cl->mark_passed_idiom_analysis();

  const int scalar_limit = 5;

  // Limit the profile trip count on the slow loop to account for the
  // scalar limit.
  float trip_cnt = MIN2<float>(slow_cl->profile_trip_cnt(), scalar_limit / 2.0f);
  slow_cl->set_profile_trip_cnt(trip_cnt);

  // tty->print_cr("slow_cl N%d (end N%d)", slow_cl->_idx,
  //               slow_cl->loopexit()->_idx);

  // Take the vectorized loop if cl->limit() >= scalar_limit.
  CmpINode *cmp = new CmpINode(cl->limit(), phase->igvn().intcon(scalar_limit));
  phase->igvn().register_new_node_with_optimizer(cmp);
  BoolNode *ge = new BoolNode(cmp, BoolTest::ge);
  phase->igvn().register_new_node_with_optimizer(ge);

  IfNode *iff = proj_true->in(0)->as_If();
  phase->igvn().replace_input_of(iff, 1, ge);
  //iff->_prob = .0f;

  TRACE(Rewrite, {
      tty->print_cr("End loop variants");
    });

  lpt->record_for_igvn();
  for(int i = lpt->_body.size() - 1; i >= 0 ; i--) {
    Node *n = lpt->_body[i];
    Node *n_clone = old_new[n->_idx];
    phase->igvn()._worklist.push(n_clone);
  }

}

bool build_stuff(Compile *C, IdealLoopTree *lpt, PhaseIdealLoop *phase,
                 PhaseIterGVN *igvn, CountedLoopNode *cl) {
  const juint VBYTES = SuperWordPolynomialWidth;
  const bool GO_PREFIX_SUM = true;

  /**************************************************************
   * Find induction and reduction phis, and right hand side of
   * scalar reduction.
   **************************************************************/
  Node *induction_phi = cl->phi();
  if (induction_phi == NULL) return false;
  TRACE(MinCond, {
      tty->print_cr("Found induction phi N%d", induction_phi->_idx);
    });


  // PhiNode holding the current value of the recurrence variable.
  PhiNode *reduction_phi = find_recurrence_phi(cl, GO_PREFIX_SUM);
  if (reduction_phi == NULL) return false;
  TRACE(MinCond, {
    tty->print_cr("Found reduction phi N%d", reduction_phi->_idx);
  });

  if (GO_PREFIX_SUM) {
    C->set_max_vector_size(16); // FIXME: Make shared for different patterns.
    return go_prefix_sum(lpt, phase, cl, phase->igvn(), induction_phi, reduction_phi);
  }

  // Right hand side of the assignment.
  Node *rhs = find_rhs(reduction_phi); //find_rhs(acc_add, reduction_phi);
  if (rhs == NULL || rhs->req() < 2) return false;
  TRACE(MinCond, {
      tty->print_cr("Found right-hand-side N%d", rhs->_idx);
    });


  /**************************************************************
   * Strip away any integer downcasts and determine type of
   * the sub-reductions.
   **************************************************************/
  BasicType recurr_bt;
  Node *start = strip_conversions(rhs, recurr_bt);
  if (start == NULL) return false;
  const Type *recurr_t = Type::get_const_basic_type(recurr_bt);

  if (!is_associative(start->Opcode())) {
    TRACE(MinCond, {
        tty->print_cr("Reduction operator %s non associative", start->Name());
      });
    return false;
  }

  /**************************************************************
   * Find the constant factor `N`.
   **************************************************************/
  JavaValue n_factor;
  NFactorInfo n_factor_info = find_n_factor(start->in(1), reduction_phi, recurr_bt, n_factor);
  if (n_factor_info == NOT_FOUND) {
    TRACE(Match, {
        tty->print_cr("Unable to find N");
        tty->print("  "); rhs->dump(" right hand side\n");
      });

    return false;
  }

  /**************************************************************
   * Build pattern instance tree.
   **************************************************************/
  const juint VLEN = VBYTES / type2aelembytes(recurr_bt);

  AlignInfo align;
  bool attempt_align = false;

  {
    ResourceMark rm;

    PatternInstance *pi = match(start->in(2), induction_phi);
    if (pi == NULL)
      return false;
    if (pi->has_alignable_load()) {
      attempt_align = true;
      align._base_addr = pi->base_addr();
      align._elem_bt = pi->elem_bt();
    }
  }

  /**************************************************************
   * Vectorize IR (point of no return).
   **************************************************************/
  if (SuperWordPolynomialMultiversion) {
    build_loop_variants(phase, lpt, cl);
  }

  // FIXME: To avoid nesting of resource marks when calling
  // `build_loop_variants` we redo the matching, avoiding
  // GrowableArray growth within nested resource marks. Maybe look
  // over the allocation strategy used for PatternInstances?
  Node *c_term;
  {
    ResourceMark rm;
    PatternInstance *pi = match(start->in(2), induction_phi);
    assert(pi != NULL, "");
    c_term = pi->generate(phase, recurr_t, VLEN);
  }

  // Split loop.
  Node_List old_new;
  Node *orig_limit = cl->limit();
  Node *new_limit = split_loop(lpt, phase, cl, VLEN, old_new);
  set_stride(cl, phase, VLEN);
  adjust_limit(cl, phase->igvn(), new_limit);

  if (C->max_vector_size() < VBYTES) {
    C->set_max_vector_size(VBYTES);
  }

  // Align first iteration.
  CountedLoopNode *pre_loop = find_pre_loop(cl);
  if (SuperWordPolynomialAlign && attempt_align) {
    align_first_main_loop_iters(phase->igvn(), pre_loop,
                                orig_limit, align, VLEN);
  }

  int op_reduce = start->Opcode();

  Node *loop_entry_ctrl = cl->skip_strip_mined()->in(LoopNode::EntryControl);

  Node *identity = phase->igvn().transform(identity_con(op_reduce));
  Node *identities = make_vector(phase, identity, recurr_t, VLEN, loop_entry_ctrl);
  //phase->set_loop(identities, lpt);
  // phase->set_ctrl(identities, loop_entry_ctrl);
  //phase->set_ctrl(identities, cl);
  //phase->set_ctrl_and_loop(identities, cl);


  Node *initial_acc = new PromoteNode(identities, reduction_phi->in(1),
                                      TypeVect::make(recurr_bt, VLEN));
  phase->igvn().register_new_node_with_optimizer(initial_acc);
  // phase->set_ctrl(initial_acc, loop_entry_ctrl);

  Node *m = make_exp_vector(phase, n_factor, VLEN, recurr_t, loop_entry_ctrl);
  Node *phi = PhiNode::make(induction_phi->in(PhiNode::Region), initial_acc);
  phase->igvn().register_new_node_with_optimizer(phi);

  // TODO: Investigate performance if replaced with vector x scalar
  // multiplication (`mulv` is a vector of scalar duplicates), it
  // should peel off a few instructions from the main loop prologue.
  Node *mul0;

  int op_mul = mul_opcode(recurr_bt);
  int op_add = add_opcode(recurr_bt);


  // If we do not multiply our recurrence variable, don't create an
  // multiplication.
  if (n_factor_info != IDENTITY) {
    Node *mulv = make_vector(phase, make_pow(n_factor, VLEN, recurr_bt), recurr_t, VLEN, loop_entry_ctrl);
    //mulv->ensure_control_or_add_prec(loop_entry_ctrl);
    //phase->set_idom(Node *d, Node *n, uint dom_depth)
    // phase->set_ctrl(mulv, loop_entry_ctrl);
    mul0 = phase->igvn().transform(VectorNode::make(op_mul, mulv, phi, VLEN, recurr_bt));
  } else {
     mul0 = phi;
  }

  Node *mul1;
  if (n_factor_info != IDENTITY) {
    mul1 = VectorNode::make(op_mul, c_term, m, VLEN, recurr_bt);
    phase->igvn().register_new_node_with_optimizer(mul1);
  } else {
    mul1 = c_term;
  }

  Node *add = VectorNode::make(op_reduce, mul0, mul1, VLEN, recurr_bt); //AddVINode(mul0, mul1, TypeVect::make(recurr_bt, VLEN));
  phase->igvn().register_new_node_with_optimizer(add);

  phi->set_req(2, add);

  Node *reduce = ReductionNode::make(op_reduce, NULL, identity, add, recurr_bt);
  phase->igvn().register_new_node_with_optimizer(reduce);

  phase->igvn().replace_node(rhs, reduce); // Replace right hand side with reduction.

  int n_unrolls = exact_log2(VLEN);
  while (n_unrolls--) {
    cl->double_unrolled_count();
  }

  return true;
}

bool polynomial_reduction_analyze(Compile* C, PhaseIdealLoop *phase, PhaseIterGVN *igvn, IdealLoopTree *lpt) {
  if (!SuperWordPolynomial) return false;
  if (!lpt->is_counted() || !lpt->is_innermost()) return false;
  CountedLoopNode *cl = lpt->_head->as_CountedLoop();
  // NOTE: If removing the `is_normal_loop` check, make sure to do
  // this check inside `split_loop`:
  if (cl->has_passed_idiom_analysis() || cl->is_vectorized_loop() ||
      !cl->is_normal_loop()) return false;

  TRACE(Candidates, {
      tty->print_cr("Initial analysis of %s::%s",
                    C->method()->get_Method()->klass_name()->as_utf8(),
                    C->method()->get_Method()->name()->as_utf8());
    });

  if (!cl->stride_is_con() || cl->stride_con() != 1) return false;
  TRACE(Candidates, { tty->print_cr("  Loop is constant unit-stride"); });

  // NOTE: Do we need/want this one?
  if (cl->range_checks_present()) return false;

  TRACE(Candidates, { tty->print_cr("  Loop has no range checks"); });

  //if (has_control_flow(cl)) return false;

  TRACE(Candidates, {
      tty->print_cr("  Loop has trivial control flow");
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
        tty->print_cr("Transformed %s::%s%s",
                      C->method()->get_Method()->klass_name()->as_utf8(),
                      C->method()->get_Method()->name()->as_utf8(),
                      C->method()->get_Method()->signature()->as_utf8());
      });

    cl->mark_passed_idiom_analysis();
    cl->mark_loop_vectorized();
    C->print_method(PHASE_AFTER_IDIOM_VECTORIZATION);
    return true;
  } else {
    TRACE(Failure, {
        tty->print_cr("Failed %s::%s%s",
                      C->method()->get_Method()->klass_name()->as_utf8(),
                      C->method()->get_Method()->name()->as_utf8(),
                      C->method()->get_Method()->signature()->as_utf8());
      });
    C->print_method(PHASE_FAILED_IDIOM_VECTORIZATION);
  }

  return false;
}

#undef TRACE
#undef ANY
