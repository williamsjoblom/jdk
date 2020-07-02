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

// The indeterminate is the
class Indeterminate {

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
  assert(induction_phi != NULL, "expected");

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

  return reduction_phi->as_Phi();
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

#define ANY NULL

class Pattern : public ResourceObj {
protected:
  static const int NO_REF = -1;
  inline void set_ref(Node *n, Node *refs[]) {
    if (_ref != NO_REF) refs[_ref] = n;
  }
public:
  int _ref;

  Pattern(int ref) : _ref(ref) {}
  virtual bool match(Node *n, Node *refs[]) = 0;

};

template<int Opcode, uint NSubpatterns>
class NodePattern : public Pattern {
public:
  Pattern* _subpatterns[NSubpatterns];

  NodePattern(int ref=NO_REF) : Pattern(ref) {
    assert(NSubpatterns == 0, "expected");
  }

  NodePattern(Pattern *p0, int ref=NO_REF) : Pattern(ref) {
    assert(NSubpatterns == 1, "expected");
    _subpatterns[0] = p0;
  }

  NodePattern(Pattern *p0, Pattern *p1, int ref=NO_REF) : Pattern(ref) {
    assert(NSubpatterns == 2, "expected");
    _subpatterns[0] = p0;
    _subpatterns[1] = p1;
  }

  NodePattern(Pattern *p0, Pattern *p1, Pattern *p2, int ref=NO_REF) : Pattern(ref) {
    assert(NSubpatterns == 3, "expected");
    _subpatterns[0] = p0; _subpatterns[1] = p1;
    _subpatterns[2] = p2;
  }

  NodePattern(Pattern *p0, Pattern *p1, Pattern *p2, Pattern *p3, int ref=NO_REF) : Pattern(ref) {
    assert(NSubpatterns == 4, "expected");
    _subpatterns[0] = p0; _subpatterns[1] = p1;
    _subpatterns[2] = p2; _subpatterns[3] = p3;
  }

  bool match(Node *n, Node* refs[]) {
    if (n->Opcode() != Opcode) return false;

    for (uint i = 0; i < n->req() && i < NSubpatterns; i++) {
      tty->print("Matching at: %d\n", i);
      Node *next = n->in(i);
      Pattern *sp = _subpatterns[i];
      if (sp != ANY) {
        if (next == NULL || !sp->match(next, refs)) return false;
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

typedef bool (*NodePred)(Node*);
class PredPattern : public Pattern {
  NodePred _pred;

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

bool pattern_match(Node *start, Node *x) {
  ResourceMark rm;

  enum {
    THE_CONSTANT,
    N_REFS
  };

  Node *refs[N_REFS];
  Pattern *p = new NodePattern<Op_SubI, 3>
    (ANY,
     new NodePattern<Op_LShiftI, 3>
     (ANY,
      new ExactNodePattern(x),
      new NodePattern<Op_ConI, 0>(THE_CONSTANT)),
     new ExactNodePattern(x));

  if (p->match(start, refs)) {
    tty->print("Successfully matched with shift distance %d\n", refs[THE_CONSTANT]->get_int());
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
  // PHI holding the current value of the `h`.
  PhiNode *reduction_phi = find_reduction_phi(cl);
  if (reduction_phi == NULL) return;
  // ADD adding the result of the current iteration to `h`
  AddNode *acc_add = find_acc_add(reduction_phi);
  if (acc_add == NULL) return;
  // Right hand side of the assignment.
  Node *rhs = find_rhs(acc_add, reduction_phi);
  if (rhs == NULL) return;

  tty->print("Patternmatching: %d\n", pattern_match(rhs->in(1), reduction_phi));

  tty->print("CL %d: reduction_phi=%d, acc_add=%d, rhs=%d, rhs[1] is mul31*phi=%d\n",
            cl->_idx,
            reduction_phi->_idx,
            acc_add->_idx,
            rhs->_idx,
            is_x_mul_31(rhs->in(1), reduction_phi));
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
