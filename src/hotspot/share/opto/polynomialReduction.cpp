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

const uint MAX_SEARCH_DEPTH = 20;


class InductionArrayRead {
public:
  Node *_head;
  Node *_tail;

  Node *_base_ptr;
  Node *_out;

  // InductionArrayRead(Node *head, Node *tail, Node *base_ptr, Node *out)
  //   : _head(head), _tail(tail), _base_ptr(base_ptr), _out(out) {}
};

// Is the given counted loop's induction variable used directly used
// in an array access?
bool get_array_access_chain(Node *head, InductionArrayRead& chain) {
  Node *tail, *base_ptr, *out;

  chain._head = head;

  Node *n = head;
  n = n->find_out_with(Op_ConvI2L);
  if (n == NULL) return false;
  n = n->find_out_with(Op_LShiftL);
  if (n == NULL) return false;

  n = n->find_out_with(Op_AddP);
  if (n == NULL) return false;
  chain._base_ptr = n->in(AddPNode::Base);

  n = n->find_out_with(Op_AddP);
  if (n == NULL) return false;

  n = n->find_out_with(Op_LoadI);
  if (n == NULL) return false;
  chain._tail = n;
  chain._out = n->raw_out(0);
  if (chain._out == NULL) return false;

  assert(chain._head != NULL && chain._tail != NULL &&
         chain._base_ptr != NULL && chain._out != NULL,
         "sanity check");

  return true;
}

PhiNode *find_reduction_phi(CountedLoopNode *cl) {
  // Find _the_ phi node connected with a control edge from the given
  // CountedLoop (excluding the phi node associated with the induction
  // variable).
  Node *induction_phi = cl->phi();
  if (induction_phi == NULL) return NULL;

  Node *reduction_phi = NULL;
  for (DUIterator it = cl->outs(); cl->has_out(it); it++) {
    Node *n = cl->out(it);
    // NOTE: maybe check that the edge we just followed is a control
    // edge?
    if (n->is_Phi() && n != induction_phi) {
      // Only allow loops with one cross-iteration dependecy for now:
      if (reduction_phi != NULL) return NULL;

      reduction_phi = n;
    }
  }

  return reduction_phi != NULL ? reduction_phi->as_Phi() : NULL;
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

AddNode *find_rhs(PhiNode *reduction_phi) {
  Node_List inputs;
  for (uint i = PhiNode::Input; i < reduction_phi->len(); i++) {
    inputs.push(reduction_phi->in(i));
  }

  Unique_Node_List visited;
  Node *bottom = find_nodes(reduction_phi, inputs, visited);

  return bottom != NULL ? bottom->isa_Add() : NULL;
}

// // Find node representing the right hand side of the reduction given
// // the `acc_add` node, and the left hand side.
// //
// // Ex. h = 31*h + a[i];
// //         ^
// //         | this is the right hand side.
// Node *find_rhs(AddNode *acc_add, Node* lhs) {
//   for (uint i = 0; i < acc_add->req(); i++) {
//     Node *in = acc_add->in(i);
//     if (in != NULL && in != lhs) {
//       return in;
//     }
//   }

//   return NULL;
// }

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

    for (uint i = 0; i < n->req() && i < NSubpatterns; i++) {
      Node *next = n->in(i);
      Pattern *sp = _subpatterns[i];
      if (sp != ANY) {
        if (next == NULL || !sp->match(next, refs)) {
          if (TRACE_MATCHING) {
            tty->print("[OpcodePattern] Matching failed for in(%d)", i);
            n->dump();
            next != NULL ? next->dump("  ") : tty->print("  NULL");
            tty->print_cr("");
          }
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
          if (TRACE_MATCHING) {
            tty->print("[Pred2Pattern] Matching failed for in(%d):", i);
            n->dump();
            next != NULL ? next->dump("  ") : tty->print("  NULL");
            tty->print_cr("");
          }
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
 * Predicates.
 ****************************************************************/
bool is_array_ptr(Node *n) {
  return n->is_Type() && n->as_Type()->type()->isa_aryptr() != NULL;
}

bool is_primitive_load(Node *n) {
  return n->is_Load() && is_java_primitive(n->bottom_type()->basic_type());
}

bool match_x_mul_31(Node *start, Node *x) {
  ResourceMark rm;

  enum {
    THE_CONSTANT,
    N_REFS
  };

  MatchRefs refs(N_REFS);
  Pattern *p = new OpcodePattern<3>
    (Op_SubI,
     ANY,                                         // Control
     new OpcodePattern<3>               // LHS
     (Op_LShiftI,
      ANY,                                            // Control
      new ExactNodePattern(x),                        // LHS
      new OpcodePattern<0>(Op_ConI, THE_CONSTANT)),     // RHS
     new ExactNodePattern(x));                    // RHS

  if (p->match(start, refs)) {
    tty->print("Successfully matched with shift distance %d\n", refs[THE_CONSTANT]->get_int());
    return true;
  } else {
    return false;
  }
}

// Array read pattern instance.
struct ArrayRead {
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
};

struct ConMul {
  jint multiplier;
};

// Match multiplication of `of`*constant.
bool match_con_mul(Node *start, Node *of, ConMul &result) {
  enum {
    SHIFT_DISTANCE,
    N_REFS
  };

  MatchRefs refs(N_REFS);
  Pattern *p = new OpcodePattern<3>
    (Op_SubI,
     ANY,
     new OpcodePattern<3>
     (Op_LShiftI,
      ANY,
      new ExactNodePattern(of),
      new OpcodePattern<0>(Op_ConI, SHIFT_DISTANCE)),
     new ExactNodePattern(of));

  if (p->match(start, refs)) {
    result.multiplier = (1 << refs[SHIFT_DISTANCE]->get_int()) - 1;
    return true;
  } else {
    return false;
  }
}

bool match_array_read(Node *start, Node *idx, ArrayRead &result) {
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
     new OpcodePattern<0>(Op_Parm, MEMORY),
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
    result._load_ctrl = refs[LOAD_CTRL];
    result._load = refs[LOAD_NODE];
    result._bt = result._load->bottom_type()->basic_type();
    result._index = idx;
    result._result = start;
    result._array_ptr = refs[ARRAY];
    result._memory = refs[MEMORY];
    result._elem_byte_size =
      1 << (refs[IDX_SHIFT_DISTANCE] != NULL
            ? refs[IDX_SHIFT_DISTANCE]->get_int()
            : 0);
    result._base_offset = refs[ARRAY_BASE_OFFSET]->get_long();

    assert(result._load_ctrl->isa_Proj(), "");
    return true;
  } else {
    return false;
  }
}

// Does the given node `n` multiply `x` by 31?
//
// This operation tend to appear on the form:
// (x << 5) - x
// [= x*32 - x = x*31]
//
// (Sub
//   (LShiftI x (ConI))
//   x
// )
bool is_x_mul_31(Node *n, Node* x) {
  if (!n->is_Sub()) return false;

  Node *lshift = n->in(1); // The first input operand of n.
  return
    n->in(2) == x &&
    lshift->Opcode() == Op_LShiftI &&
    lshift->in(1) == x &&
    lshift->in(2)->Opcode() == Op_ConI &&
    lshift->in(2)->get_int() == 5;
}

// Does one of the incoming edges of `phi` depend on its outgoing
// edge?
bool is_self_dependent(PhiNode *phi) {
  Node_List inputs;
  for (uint i = PhiNode::Input; i < phi->len(); i++) {
    inputs.push(phi->in(i));
  }

  Unique_Node_List visited;
  Node *bottom = find_nodes(phi, inputs, visited);
  return bottom != NULL;
}

GrowableArray<InductionArrayRead> get_array_access_chains(Node *phi) {
  GrowableArray<InductionArrayRead> chains;

  for (DUIterator it = phi->outs(); phi->has_out(it); it++) {
    Node* n = phi->out(it);
    if (n->Opcode() == Op_CastII) {
      InductionArrayRead chain;
      if (get_array_access_chain(n, chain)) {
        chains.append(chain);
      }
    }
  }

  return chains;
}

/****************************************************************
 * Main-loop patching
 ****************************************************************/
void set_stride(CountedLoopNode *cl, PhaseIdealLoop *phase, jint new_stride) {
  assert(cl->stride_is_con(), "setting stride for non const stride loop");

  ConNode *stride = ConNode::make(TypeInt::make(new_stride));
  phase->igvn().register_new_node_with_optimizer(stride);

  Node *incr = cl->incr();
  if (incr != NULL && incr->req() == 3) {
    phase->igvn().replace_input_of(incr, 2, stride);
  } else {
    ShouldNotReachHere();
  }
}

void adjust_limit_to_vec_size(CountedLoopNode *cl, PhaseIdealLoop *phase, jint vec_size) {
  // WARNING: (limit - stride) may underflow!!!
  const uint LIMIT = 2;
  Node *cmp = cl->loopexit()->cmp_node();
  assert(cmp != NULL && cmp->req() == 3, "no loop limit found");
  Node *limit = cmp->in(LIMIT);

  Node *new_stride = ConNode::make(TypeInt::make(vec_size));
  Node *adjusted_limit = new SubINode(limit, new_stride);

  assert(adjusted_limit != NULL, "adj limit");

  phase->igvn().register_new_node_with_optimizer(new_stride);
  phase->igvn().register_new_node_with_optimizer(adjusted_limit);

  phase->igvn().replace_input_of(cmp, LIMIT, adjusted_limit);
}

// Is `cl` a polynomial reduction?
bool is_polynomial_reduction(CountedLoopNode *cl) {
  PhiNode *reduction_phi = find_reduction_phi(cl);
  return reduction_phi != NULL && is_self_dependent(reduction_phi);
}

// Make int vector containing [init, init, ..., init]
VectorNode *make_vector(PhaseIdealLoop *phase, jint init, juint vec_size) {
  ConNode *init_con = ConNode::make(TypeInt::make(init));
  VectorNode *acc = VectorNode::scalar2vector(init_con, vec_size, TypeInt::INT);

  phase->igvn().register_new_node_with_optimizer(init_con);
  phase->igvn().register_new_node_with_optimizer(acc);

  return acc;
}

// Make 4 int vector containing [n^3, n^2, n^1, n^0].
VectorNode *make_exp_vector(PhaseIdealLoop *phase, jint n, juint vec_size) {
  assert(vec_size == 4 || vec_size == 8, "expected");

  if (vec_size == 4) {
    ConNode *b = ConNode::make(TypeLong::make(((n * n * n)) | ((long)n * n << 32)));
    ConNode *a = ConNode::make(TypeLong::make(n | ((long)1 << 32)));
    VectorNode *con = VectorNode::scalars2vector(a, b);
    phase->igvn().register_new_node_with_optimizer(a);
    phase->igvn().register_new_node_with_optimizer(b);
    phase->igvn().register_new_node_with_optimizer(con);
    return con;
  } else if (vec_size == 8) {
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

jint my_pow(jint n, jint exp) {
  jint result = 1;
  while (exp--) {
    result *= n;
  }
  return result;
}

Node *build_array_load(PhaseIdealLoop *phase, ArrayRead& array_read, uint vlen) {
  //BasicType vector_type = array_read._load->
  LoadNode *load = array_read._load->as_Load();
  BasicType load_type = array_read._bt;
  BasicType elem_type = load->memory_type();

  tty->print_cr("load: %s, elem: %s", type2name(load_type), type2name(elem_type));

  // No implicit cast.
  if (elem_type == load_type) {
     Node *arr = LoadVectorNode::make(
        array_read._load->Opcode(), array_read._load->in(LoadNode::Control),
        array_read._memory, array_read._load->in(LoadNode::Address),
        array_read._load->adr_type(), vlen, elem_type);
     phase->igvn().register_new_node_with_optimizer(arr, NULL);
     return arr;
  } else if (elem_type == T_BYTE && load_type == T_INT) {
    Node *arr = ShortLoadVectorNode::make(
        array_read._load->Opcode(), array_read._load->in(LoadNode::Control),
        array_read._memory, array_read._load->in(LoadNode::Address),
        array_read._load->adr_type(), vlen, elem_type);
     phase->igvn().register_new_node_with_optimizer(arr, NULL);
     return arr;
  }

  ShouldNotReachHere();
  return NULL;
}

// NOTE: move to IdealLoopTree / loopTransform.cpp?
bool build_stuff(Compile *C, IdealLoopTree *lpt, PhaseIdealLoop *phase, PhaseIterGVN *igvn, CountedLoopNode *cl) {
  const juint VLEN = 8;

  Node *induction_phi = cl->phi();
  if (induction_phi == NULL) return false;
  NOT_PRODUCT(tty->print_cr("Found induction phi N%d", induction_phi->_idx));

  // PHI holding the current value of the `h`.
  PhiNode *reduction_phi = find_reduction_phi(cl);
  if (reduction_phi == NULL) return false;
  NOT_PRODUCT(tty->print_cr("Found reduction phi N%d", reduction_phi->_idx));
  // ADD adding the result of the current iteration to `h`
  // AddNode *acc_add = find_rhs(reduction_phi);
  // if (acc_add == NULL) return false;
  // if (VERBOSE) tty->print_cr("Found acc_add N%d", acc_add->_idx);

  // Right hand side of the assignment.
  Node *rhs = find_rhs(reduction_phi); //find_rhs(acc_add, reduction_phi);
  if (rhs == NULL) return false;
  NOT_PRODUCT(tty->print_cr("Found right-hand-side N%d", rhs->_idx));

  ConMul con_mul;
  ArrayRead array_read;

  bool ok1 = match_con_mul(rhs->in(1), reduction_phi, con_mul);
  bool ok2 = match_array_read(rhs->in(2), induction_phi, array_read);

  NOT_PRODUCT(tty->print_cr("con_mul? %d, array_read? %d", ok1, ok2));

  if (!ok1 || !ok2) return false;

  NOT_PRODUCT(tty->print_cr("APPLYING TRANSFORMATION! m = %d", con_mul.multiplier));

  // Build post-loop for the remaining iterations that does not fill
  // up a full vector.
  // Node *one = ConINode::make(1);
  // Node *post_init_trip = new AddINode(cl->phi(), one);
  // phase->igvn().register_new_node_with_optimizer(one);
  // phase->igvn().register_new_node_with_optimizer(post_init_trip);

  CountedLoopNode* post_head;
  {
    Node_List old_new;
    phase->insert_post_loop(lpt, old_new, cl, cl->loopexit(), cl->incr(),
                            cl->limit(), post_head);
  }
  post_head->loopexit()->_prob = 1.0f / (VLEN - 1);

  // Adjust main loop stride and limit.
  set_stride(cl, phase, VLEN);
  adjust_limit_to_vec_size(cl, phase, VLEN);
  // post_head->phi()->set_req(1, cl->phi());


  NOT_PRODUCT(tty->print_cr("cl->stride() = %d", cl->stride()->_idx));

  const uint VECTOR_BYTE_SIZE = VLEN * 4; // 4 4byte ints
  if (C->max_vector_size() < VECTOR_BYTE_SIZE) {
    C->set_max_vector_size(VECTOR_BYTE_SIZE);
  }



  // Node *out_phi = cl->find(155);
  // assert(out_phi->isa_Phi(), "a phi");

  // Constant multiplier
  Node *mulv = make_vector(phase, my_pow(con_mul.multiplier, VLEN), VLEN);

  Node *arr = build_array_load(phase, array_read, VLEN);

  Node *initial_acc = make_vector(phase, 0, VLEN);
  Node *m = make_exp_vector(phase, con_mul.multiplier, VLEN);

  // NOTE: WAS reduction_phi->in(PhiNode::Region)
  Node *phi = PhiNode::make(induction_phi->in(PhiNode::Region), initial_acc);
  phase->igvn().register_new_node_with_optimizer(phi);

  Node *mul0 = new MulVINode(mulv, phi, TypeVect::make(T_INT, VLEN));
  phase->igvn().register_new_node_with_optimizer(mul0);
  Node *mul1 = new MulVINode(arr, m, TypeVect::make(T_INT, VLEN));
  phase->igvn().register_new_node_with_optimizer(mul1);

  Node *add = new AddVINode(mul0, mul1, TypeVect::make(T_INT, VLEN));
  phase->igvn().register_new_node_with_optimizer(add);

  phi->set_req(2, add);

  // Replace with initial reduction phi value:
  ConNode *reduce_base = ConNode::make(TypeInt::make(0));
  Node *reduce = ReductionNode::make(Op_AddI, NULL, reduce_base, add, T_INT);

  phase->igvn().register_new_node_with_optimizer(reduce_base, NULL);
  phase->igvn().register_new_node_with_optimizer(reduce, NULL);

  phase->igvn().replace_node(rhs, reduce); // Replace right hand side with reduction.
  // phase->igvn().replace_input_of(acc_add, 2, reduce);

  cl->mark_polynomial_reduction();
  cl->mark_loop_vectorized();
  cl->double_unrolled_count();
  cl->double_unrolled_count();
  cl->double_unrolled_count();

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
  if (!cl->stride_is_con() || cl->is_polynomial_reduction() ||
      !cl->is_normal_loop()) return false;

  bool inHashCode = strcmp(C->method()->name()->as_utf8(), "stringHashCode") == 0;

  if (build_stuff(C, lpt, phase, igvn, cl)) {
    tty->print_cr("Transformed %s in class %s", C->method()->get_Method()->name()->as_utf8(),
                  C->method()->get_Method()->klass_name()->as_utf8());
    C->method()->get_Method()->set_dont_inline(true);
    return true;
  }
    // assert(C->method()->name()->equals("asd"), "");

  return false;

  //ResourceMark rm;
  // GrowableArray<InductionArrayRead> chains = get_array_access_chains(cl->phi());

  // if (chains.is_nonempty()) {
  //   tty->print("-");
  //   for (GrowableArrayIterator<InductionArrayRead> it = chains.begin();
  //        it != chains.end(); ++it) {
  //     tty->print("Found array access with induction variable LoopNode: %d, "
  //                "base_ptr: %d, out: %d\n",
  //               cl->_idx, (*it)._base_ptr->_idx, (*it)._out->_idx);
  //   }
  // }

  // tty->print("Found counted loop idx: %d, phi-idx: %d\n", cl->_idx, cl->phi()->_idx);
  // tty->print(" With outs idx: ");
  // for (DUIterator it = cl->outs(); cl->has_out(it); it++) {
  //   // tty->print("%d ", cl->out(it)->_idx);
  // }
  // tty->print("\n");
}

#undef ANY
