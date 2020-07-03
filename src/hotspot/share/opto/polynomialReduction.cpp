#include "precompiled.hpp"
#include "opto/polynomialReduction.hpp"
#include "opto/loopnode.hpp"
#include "opto/node.hpp"
#include "opto/addnode.hpp"
#include "opto/memnode.hpp"
#include "opto/mulnode.hpp"
#include "opto/connode.hpp"

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

AddNode *find_acc_add(PhiNode *reduction_phi) {
  Node_List inputs;
  for (uint i = PhiNode::Input; i < reduction_phi->len(); i++) {
    inputs.push(reduction_phi->in(i));
  }

  Unique_Node_List visited;
  Node *bottom = find_nodes(reduction_phi, inputs, visited);

  if (!bottom->is_Add()) return NULL;
  return bottom->as_Add();
}

// Find node representing the right hand side of the reduction given
// the `acc_add` node, and the left hand side.
//
// Ex. h = 31*h + a[i];
//         ^
//         | this is the right hand side.
Node *find_rhs(AddNode *acc_add, Node* lhs) {
  for (uint i = 0; i < acc_add->req(); i++) {
    Node *in = acc_add->in(i);
    if (in != NULL && in != lhs) {
      return in;
    }
  }

  return NULL;
}

#define ANY (Pattern*)NULL

class Pattern : public ResourceObj {
protected:
  static const int NO_REF = -1;
  inline void set_ref(Node *n, Node *refs[]) {
    if (_ref != NO_REF) refs[_ref] = n;
  }
public:
  int _ref;

  Pattern(int ref) : _ref(ref) {}
  virtual ~Pattern() {}
  virtual bool match(Node *n, Node *refs[]) = 0;
};

// TODO: Make Opcode a field instead of a template parameter.
template<int Opcode, uint NSubpatterns>
class OpcodePattern : public Pattern {
public:
  Pattern* _subpatterns[NSubpatterns];

  OpcodePattern(int ref=NO_REF) : Pattern(ref) {
    assert(NSubpatterns == 0, "expected");
  }

  OpcodePattern(Pattern *p0, int ref=NO_REF) : Pattern(ref) {
    assert(NSubpatterns == 1, "expected");
    _subpatterns[0] = p0;
  }

  OpcodePattern(Pattern *p0, Pattern *p1, int ref=NO_REF) : Pattern(ref) {
    assert(NSubpatterns == 2, "expected");
    _subpatterns[0] = p0;
    _subpatterns[1] = p1;
  }

  OpcodePattern(Pattern *p0, Pattern *p1, Pattern *p2, int ref=NO_REF) : Pattern(ref) {
    assert(NSubpatterns == 3, "expected");
    _subpatterns[0] = p0; _subpatterns[1] = p1;
    _subpatterns[2] = p2;
  }

  OpcodePattern(Pattern *p0, Pattern *p1, Pattern *p2, Pattern *p3, int ref=NO_REF) : Pattern(ref) {
    assert(NSubpatterns == 4, "expected");
    _subpatterns[0] = p0; _subpatterns[1] = p1;
    _subpatterns[2] = p2; _subpatterns[3] = p3;
  }

  bool match(Node *n, Node* refs[]) {
    if (n->Opcode() != Opcode) return false;

    for (uint i = 0; i < n->req() && i < NSubpatterns; i++) {
      Node *next = n->in(i);
      Pattern *sp = _subpatterns[i];
      if (sp != ANY) {
        if (next == NULL || !sp->match(next, refs)) {
          return false;
        }
      }
    }

    set_ref(n, refs);
    return true;
  }
};

class ExactNodePattern : public Pattern {
public:
  // Only match this exact node.
  Node *_n;

  ExactNodePattern(Node *n) : Pattern(NO_REF), _n(n) {};

  bool match(Node *n, Node *refs[]) {
    return n == _n;
  }
};

typedef bool (*NodePred)(Node *);
class PredPattern : public Pattern {
private:
  NodePred _pred;
public:
  PredPattern(NodePred pred, int ref=NO_REF) : Pattern(ref), _pred(pred) {}

  bool match(Node *n, Node *refs[]) {
    if (_pred(n)) {
      set_ref(n, refs);
      return true;
    } else {
      return false;
    }
  }
};

// Unconditionally matches a node, saving it as a ref.
class CapturePattern : public Pattern {
public:
  CapturePattern(int ref) : Pattern(ref) {}
  bool match(Node *n, Node *refs[]) {
    set_ref(n, refs);
    return true;
  }
};

bool is_array_ptr(Node *n) {
  return n->is_Type() && n->as_Type()->type()->isa_aryptr() != NULL;
}

bool match_x_mul_31(Node *start, Node *x) {
  ResourceMark rm;

  enum {
    THE_CONSTANT,
    N_REFS
  };

  Node *refs[N_REFS];
  Pattern *p = new OpcodePattern<Op_SubI, 3>
    (ANY,                                         // Control
     new OpcodePattern<Op_LShiftI, 3>               // LHS
     (ANY,                                            // Control
      new ExactNodePattern(x),                        // LHS
      new OpcodePattern<Op_ConI, 0>(THE_CONSTANT)),     // RHS
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

  Node *refs[N_REFS];
  Pattern *p = new OpcodePattern<Op_SubI, 3>(
      ANY,
      new OpcodePattern<Op_LShiftI, 3>
      (ANY,
       new ExactNodePattern(of),
       new OpcodePattern<Op_ConI, 0>(SHIFT_DISTANCE)),
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
    ARRAY,
    MEMORY,
    IDX_SHIFT_DISTANCE,
    ARRAY_BASE_OFFSET,
    CAST_II,

    N_REFS
  };

  Node *refs[N_REFS];
  Pattern *p = new OpcodePattern<Op_LoadI, 3>
    (ANY,
     new OpcodePattern<Op_Parm, 0>(MEMORY),
     new OpcodePattern<Op_AddP, 4>
     (ANY,
      ANY,
      new OpcodePattern<Op_AddP, 4>
      (ANY,                            // AddP: Control
       ANY,                            // AddP: Base
       new PredPattern(is_array_ptr, ARRAY), // AddP: Address
       new OpcodePattern<Op_LShiftL, 3>  // AddP: Offset
       (ANY,                           // LShiftL: Control
        new OpcodePattern<Op_ConvI2L, 2> // LShiftL: Left-hand side
        (ANY,                          // ConvI2L: Control
         new OpcodePattern<Op_CastII, 2> // ConvI2L: Data
         (ANY,                         // CastII:  Control
          new ExactNodePattern(idx),   // CastII:  Index
          CAST_II)),
        new OpcodePattern<Op_ConI, 0>(IDX_SHIFT_DISTANCE))),
      new OpcodePattern<Op_ConL, 0>(ARRAY_BASE_OFFSET)));

  if (p->match(start, refs)) {
    //tty->print("ISARY? %d\n", (bool)refs[ARRAY]->as_Type()->type()->isa_aryptr());

    result._index = idx;
    result._result = start;
    result._array_ptr = refs[ARRAY];
    result._memory = refs[MEMORY];
    result._elem_byte_size = 1 << refs[IDX_SHIFT_DISTANCE]->get_int();
    result._base_offset = refs[ARRAY_BASE_OFFSET]->get_long();

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


// Is `cl` a polynomial reduction?
bool is_polynomial_reduction(CountedLoopNode *cl) {
  PhiNode *reduction_phi = find_reduction_phi(cl);

  return reduction_phi != NULL && is_self_dependent(reduction_phi);
}

void build_stuff(CountedLoopNode *cl) {
  Node *induction_phi = cl->phi();
  if (induction_phi == NULL) return;

  // PHI holding the current value of the `h`.
  PhiNode *reduction_phi = find_reduction_phi(cl);
  if (reduction_phi == NULL) return;
  // ADD adding the result of the current iteration to `h`
  AddNode *acc_add = find_acc_add(reduction_phi);
  if (acc_add == NULL) return;
  // Right hand side of the assignment.
  Node *rhs = find_rhs(acc_add, reduction_phi);
  if (rhs == NULL) return;

  ConMul con_mul;
  ArrayRead array_read;

  bool ok1 = match_con_mul(rhs->in(1), reduction_phi, con_mul);
  bool ok2 = match_array_read(rhs->in(2), induction_phi, array_read);

  tty->print("Matched CountedLoop %d\n", cl->_idx);
  if (ok1) {
    tty->print("  Reduction variable multiplier by: %d\n", con_mul.multiplier);
  }

  if (ok2) {
    tty->print("  Array read: i%d %d[%d]\n", array_read._elem_byte_size * 8,
              array_read._array_ptr->_idx, array_read._index->_idx);
  }

  // tty->print("Patternmatching *32: %d\n", match_con_mul(rhs->in(1), reduction_phi, con_mul));
  // tty->print("Patternmatching a[i]: %d\n", match_array_read(rhs->in(2), reduction_phi, array_read));

  // tty->print("CL %d: reduction_phi=%d, acc_add=%d, rhs=%d, rhs[1] is mul31*phi=%d\n",
  //           cl->_idx,
  //           reduction_phi->_idx,
  //           acc_add->_idx,
  //           rhs->_idx,
  //           is_x_mul_31(rhs->in(1), reduction_phi));
}

void polynomial_reduction_analyze(IdealLoopTree *lpt) {

  if (!lpt->is_counted() || !lpt->is_innermost()) return;
  CountedLoopNode *cl = lpt->_head->as_CountedLoop();
  if (!cl->stride_is_con() || cl->is_polynomial_reduction()) return;

  if (is_polynomial_reduction(cl)) {
    cl->mark_polynomial_reduction();
  }

  build_stuff(cl);

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
