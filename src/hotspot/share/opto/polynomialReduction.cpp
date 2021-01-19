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
#include "opto/idiomPattern.hpp"
#include "opto/idiomMatch.hpp"

/****************************************************************
 * Forward declarations.
 ***************************************************************/
struct PatternInstance;

const int TRACE_OPTS = MinCond | // Match | MinCond
  NoTraceOpts;

/****************************************************************
 * Map dense Node indices to PatternInstances.
 ****************************************************************/
class Node2Instance : public ResourceObj {
  GrowableArray<PatternInstance *> map;

  void annotate(const Node *node, PatternInstance *with_pattern) {
    map.at_put_grow(node->_idx, with_pattern);
  }

  PatternInstance *at(const Node *node) {
    assert(map.length() > 0, "");
    if ((uint32_t) map.length() <= node->_idx) return NULL;
    assert(node->_idx <= INT32_MAX, "");
    return map.at(node->_idx);
  }
};

/****************************************************************
 * Tracing.
 ****************************************************************/


/****************************************************************
 * Minimum matching condition.
 ****************************************************************/
bool has_control_flow(CountedLoopNode *cl) {
  // TODO: Bad negation?
  Node *exit = cl->loopexit();
  return exit->in(0) == cl;
}

PhiNode *find_recurrence_phi(CountedLoopNode *cl, bool memory) {
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

    if (n->is_Phi() && n != induction_phi //&&
        // (primitive_reduction || memory_reduction)
        ) {
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
// Node *find_nodes(Node *start, Node_List &nodes, Unique_Node_List
// &visited, uint depth=0) {
//   if (depth >= MAX_SEARCH_DEPTH || visited.member(start)) return NULL;
//   if (nodes.contains(start)) return start;

//   visited.push(start);

//   for (DUIterator it = start->outs(); start->has_out(it); it++) {
//     Node *n = start->out(it);
//     Node *result = find_nodes(n, nodes, visited, depth + 1);
//     if (result != NULL) return result;
//   }

//   return NULL;
// }

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

/****************************************************************
 * Pattern matching.
 ****************************************************************/

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


/****************************************************************
 * Pattern instance alignment.
 ****************************************************************/

// struct AlignInfo {
//   Node *_base_addr;
//   BasicType _elem_bt;
// };

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
                                 AlignInfo *align, int vlen) {
  // tty->print_cr("Aligning main loop: N%d + %d, preferred align: %d bits",
  //               align->_base_ptr->_idx, align->_base_offset,
  //               align->_preferred_align * 8);
  Node *base = align->_base_ptr;
  Node *base_offset = igvn.longcon(align->_base_offset);
  Node *first_elem_ptr = igvn.transform(new AddPNode(base, base, base_offset));
  Node *x_elem_ptr = igvn.transform(new CastP2XNode(NULL, first_elem_ptr));
#ifdef _LP64
  // Cast long pointer to integer in case of 64 bit architecture.
  // Since alignment is determined by the last few bits, we only
  // need the least significant part of the pointer anyways.
  x_elem_ptr = new ConvL2INode(x_elem_ptr);
  igvn.register_new_node_with_optimizer(x_elem_ptr);
#endif
  // uint target_align = type2aelembytes(align._elem_bt)*vlen;
  Node *target_align_con = igvn.intcon(align->_preferred_align);

  Node *new_limit = pre_loop_align_limit(igvn, target_align_con, x_elem_ptr,
                                         align->_bytes_per_iter);
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

bool is_semiassociative(int opc) {
  if (is_associative(opc)) return true;

  switch (opc) {
  case Op_SubI:
  case Op_SubL:
  case Op_SubF:
  case Op_SubD:
    return true;
  default:
    return false;
  }
}

int reduction_opcode(int opc) {
  assert(is_semiassociative(opc), "operator not semi-associative");
  switch (opc) {
  case Op_SubI: return Op_AddI;
  case Op_SubL: return Op_AddL;
  case Op_SubF: return Op_AddF;
  case Op_SubD: return Op_AddD;
  default:
    assert(is_associative(opc), "operator not associative");
    return opc;
  }
}

// Return a constant holding the identity of the given scalar opcode.
Node *identity_con(int opc) {
  assert(is_semiassociative(opc), "expected");
  switch (opc) {
  // Additive identity (0):
  case Op_AddI:
  case Op_SubI:
  case Op_OrI:
  case Op_XorI:
  case Op_MaxI:
  case Op_MinI:
    return ConNode::make(TypeInt::make(0));
  case Op_AddL:
  case Op_SubL:
  case Op_OrL:
  case Op_XorL:
    return ConNode::make(TypeLong::make(0));
  case Op_AddF:
  case Op_SubF:
  case Op_MaxF:
  case Op_MinF:
    return ConNode::make(TypeF::make(0));
  case Op_AddD:
  case Op_SubD:
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
    Node *a = ConNode::make(TypeLong::make(make_exp_vector_part(0, n, elem_bytes, bt)));
    Node *b = ConNode::make(TypeLong::make(make_exp_vector_part(1, n, elem_bytes, bt)));
    Node *c = ConNode::make(TypeLong::make(make_exp_vector_part(2, n, elem_bytes, bt)));
    Node *d = ConNode::make(TypeLong::make(make_exp_vector_part(3, n, elem_bytes, bt)));
    Node *con_lo = VectorNode::scalars2vector(d, c, bt);
    Node *con_hi = VectorNode::scalars2vector(b, a, bt);
    Node *con = VectorNode::scalars2vector(con_lo, con_hi, bt);
    if (control != NULL) {
      con_lo->set_req(0, control);
      con_hi->set_req(0, control);
      con->set_req(0, control);
      igvn.register_new_node_with_optimizer(con_lo);
      igvn.register_new_node_with_optimizer(con_hi);
      igvn.register_new_node_with_optimizer(con);
    }

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
  Node *adjusted_opaq = new Opaque1Node(phase->C, adjusted_limit);
  phase->igvn().register_new_node_with_optimizer(adjusted_limit);
  phase->igvn().register_new_node_with_optimizer(adjusted_opaq);
  phase->igvn().replace_input_of(zero_cmp, 2, adjusted_opaq);

  return adjusted_limit;
}

// Set stride of the given loop.
void set_stride(CountedLoopNode *cl, PhaseIdealLoop *phase, jint new_stride) {
  assert(cl->stride_is_con(), "setting stride for non const stride loop");

  ConNode *stride = ConNode::make(TypeInt::make(new_stride));
  phase->igvn().register_new_node_with_optimizer(stride);

  cl->set_profile_trip_cnt(cl->profile_trip_cnt() / new_stride);
  // cl->set_trip_count(cl->trip_count() / new_stride);

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

float epilogue_cost(int vlen, BasicType bt) {
  // TODO:
  return 0;
}

int round_up(int number, int multiple) {
  int remainder = number % multiple;
  return remainder == 0 ? number : number + multiple - remainder;
}

// Return an estimation of the minumum number of trips that has to be
// taken for the vectorized loop to be profitable.
int min_profitable_trips(int vlen, BasicType bt,
                         PatternInstance* pi,
                         int max_pre_iters) {
  return 1;
  float missed_unroll_trip_cost = 2*vlen;
  float cost = missed_unroll_trip_cost;
  float ilp_trip_cost = 0;

  if (pi->op() == PatternInstance::Reduction) {
    ReductionPattern *reduction = static_cast<ReductionPattern*>(pi);
    if (!reduction->_scaled) {
      switch (bt) {
      case T_DOUBLE:
        return (vlen == 2 ? 11 : 21) + max_pre_iters;
      case T_FLOAT:
        return (vlen == 4 ? 12 : 24) + max_pre_iters;
      case T_INT:
        return (vlen == 4 ? 40 : 80) + max_pre_iters;
      // case T_SHORT: return (vlen == 8 ? )
      default: break;
      }
    } else {
      switch (bt) {
      case T_INT:
        return (vlen == 4 ? 12 : 24) + max_pre_iters;
      case T_BYTE:
        return 0;
      default: break;
      }
    }
  }

  return 2*vlen + max_pre_iters;
}

// Clone the loop to be vectorized, where the cloned, unvectorized,
// loop is picked for low tripcounts.
Node *build_scalar_variant(PhaseIdealLoop *phase, IdealLoopTree *lpt,
                          CountedLoopNode *cl, BasicType bt, int vlen,
                          PatternInstance *pi, int max_pre_iters=1) {
  //cl->mark_is_multiversioned();
  TRACE(Rewrite, {
      tty->print_cr("Start loop variants");
    });

  Node_List old_new;
  // Projection node for the vectorized loop.
  ProjNode *proj_true = phase->create_slow_version_of_loop(
    lpt, old_new, Op_If,
    PhaseIdealLoop::CloneIncludesStripMined);

  CountedLoopNode *slow_cl = old_new[cl->_idx]->as_CountedLoop();
  slow_cl->mark_passed_idiom_analysis();
  // tty->print_cr("     Slow CL idx: %d", slow_cl->_idx);

  const int scalar_limit = min_profitable_trips(vlen, bt, pi, max_pre_iters);

  // Limit the profile trip count on the slow loop to account for the
  // scalar limit.
  float trip_cnt = MIN2<float>(slow_cl->profile_trip_cnt(), scalar_limit);
  // slow_cl->set_profile_trip_cnt(trip_cnt);

  // Take the vectorized loop if cl->limit() >= scalar_limit.
  CmpINode *cmp = new CmpINode(cl->limit(), phase->igvn().intcon(scalar_limit));
  phase->igvn().register_new_node_with_optimizer(cmp);
  BoolNode *gt = new BoolNode(cmp, BoolTest::gt);
  phase->igvn().register_new_node_with_optimizer(gt);

  IfNode *iff = proj_true->in(0)->as_If();
  phase->igvn().replace_input_of(iff, 1, gt);

  TRACE(Rewrite, {
      tty->print_cr("End loop variants");
    });

  lpt->record_for_igvn();
  for(int i = lpt->_body.size() - 1; i >= 0 ; i--) {
    Node *n = lpt->_body[i];
    Node *n_clone = old_new[n->_idx];
    phase->igvn()._worklist.push(n_clone);
  }

  return proj_true;
}

struct LoopVariantInfo {
  CountedLoopNode *variant;
  Node *start;
};


void rewrite_loop(IdealLoopTree *lpt, PhaseIdealLoop *phase, CountedLoopNode *cl,
                  PatternInstance *pi, Node *start, const Type* recurr_t, int VLEN,
                  Node *reduction_phi, Node *induction_phi) {
  Node_List old_new;
  Node *orig_limit = cl->limit();
  Node *new_limit = split_loop(lpt, phase, cl, VLEN, old_new);
  set_stride(cl, phase, VLEN);
  adjust_limit(cl, phase->igvn(), new_limit);

  Node *loop_entry_ctrl = cl->skip_strip_mined()->in(LoopNode::EntryControl);
  Node *start_replace = pi->generate(phase, recurr_t, VLEN, reduction_phi,
                                     induction_phi, loop_entry_ctrl, old_new,
                                     lpt);
  assert(start_replace != NULL, "no ir generated");
  //igvn.register_new_node_with_optimizer(start_replace);
  phase->igvn().replace_node(start, start_replace);
  phase->igvn().remove_dead_node(start);
}

bool go_prefix_sum(IdealLoopTree *lpt, PhaseIdealLoop *phase, CountedLoopNode *cl, PhaseIterGVN &igvn,
                   Node *induction_phi, Node *reduction_phi) {

  Node *start = reduction_phi->in(2);
  PatternInstance* pi = match(start, induction_phi);
  if (pi == NULL) return false;
#ifndef PRODUCT
    tty->print_cr("Before reduction");
    pi->dump(4);
#endif

  pi = pi->reduce(reduction_phi, induction_phi);

  if (!pi->is_rewritable_idiom()) {
#ifndef PRODUCT
    tty->print_cr("Failed idiom");
    pi->dump(4);
#endif
    return false;
  }

  const BasicType recurr_bt = pi->velt();
  const Type *recurr_t = Type::get_const_basic_type(recurr_bt);
  const int VLEN = SuperWordPolynomialWidth / type2aelembytes(recurr_bt);

  // Skip vectorization when trip-count is expected to be below profitability.
  int pre_iters = SuperWordPolynomialAlign ? VLEN : 1;
  lpt->compute_profile_trip_cnt(phase);
  if (round(cl->profile_trip_cnt()) < min_profitable_trips(VLEN, recurr_bt, pi, pre_iters)) {
    tty->print_cr("PTC bailout (actual %f, target %d pres %d)",
                  round(cl->profile_trip_cnt()),
                  min_profitable_trips(VLEN, recurr_bt, pi, pre_iters),
                  pre_iters);
    return false;
  }
  assert(is_power_of_2(VLEN), "santiy");
  phase->C->set_max_vector_size(SuperWordPolynomialWidth); // FIXME: Make shared for different patterns.

  Node *loop_entry_ctrl = cl->in(LoopNode::EntryControl);
  //LoopVariantInfo aggressive;
  if (SuperWordPolynomialMultiversion) {
    loop_entry_ctrl = build_scalar_variant(phase, lpt, cl, recurr_bt, VLEN, pi, pre_iters);
  }


  Node_List old_new;
  Node *orig_limit = cl->limit();
  Node *orig_incr = cl->incr();
  Node *new_limit = split_loop(lpt, phase, cl, VLEN, old_new);
  set_stride(cl, phase, VLEN);
  adjust_limit(cl, phase->igvn(), new_limit);

  if (SuperWordPolynomialAlign) {
    AlignInfo *align_info = pi->align_info(VLEN);

    if (align_info != NULL) {
      align_first_main_loop_iters(igvn, find_pre_loop(cl), orig_limit,
                                  align_info, VLEN);
    }
  }


  Node *start_replace = pi->generate(phase, recurr_t, VLEN, reduction_phi,
                                     induction_phi, loop_entry_ctrl, old_new,
                                     lpt);

  // start_replace->set_req(0, cl->loopexit()->proj_out(false));
  assert(start_replace != NULL, "no ir generated");
  // for (DUIterator_Fast imax, i = reduction_phi->fast_outs(imax); i < imax; i++) {
  //   Node *out = reduction_phi->fast_out(i);
  //   igvn.rehash_node_delayed(out);
  //   out->set_in(2, start_replace);
  // }

  // igvn.rehash_node_delayed(reduction_phi);
  // reduction_phi->set_req(2, reduction_phi->in(1));
  // phase->recompute_dom_depth();

  // igvn.replace_node(reduction_phi, start_replace);

  igvn.replace_node(start, start_replace);

  lpt->record_for_igvn();
  // igvn.replace_node(reduction_phi, start_replace);

  //phase->set_ctrl(start_replace, cl->loopexit()->proj_out(false));
  //igvn.remove_dead_node(start);

  // if (pi->op() == PatternInstance::Reduction) {
  //   // NOTE: Ugly, possibly very unsafe hack, removing the need to
  //   // perform a horizontal vector reduction every iteration.
  //   if (Node *sp = start_replace->find_out_with(Op_SafePoint)) {
  //     sp->replace_edge(start_replace, old_new[start->_idx]);
  //     sp->replace_edge(orig_incr, old_new[orig_incr->_idx]);
  //   }
  // }

  static int total_vectorized_loops = 0;
  Compile *c = igvn.C;
  Method *m = c->method()->get_Method();
  if (c->_compile_id != m->_n_vectorized_loops_comp_idx) {
    m->_n_vectorized_loops_comp_idx = c->_compile_id;
    total_vectorized_loops -= m->_n_vectorized_loops;
    m->_n_vectorized_loops = 0;
  }
  // cl->set_slp_max_unroll(VLEN);
  m->_n_vectorized_loops++;
  total_vectorized_loops++;


  int n_doublings = exact_log2(VLEN);
  while (n_doublings--) {
    cl->double_unrolled_count();
  }

  tty->print_cr("idiom in %s::%s (ptc: %f) (total: %d) (min trips: %d) (cl idx: %d)",
                m->klass_name()->as_utf8(),
                m->name()->as_utf8(),
                cl->profile_trip_cnt(),
                total_vectorized_loops,
                min_profitable_trips(VLEN, recurr_bt, pi, 1),
                cl->_idx);

  return true;
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
    return go_prefix_sum(lpt, phase, cl, phase->igvn(), induction_phi, reduction_phi);
  }

  // Right hand side of the assignment.
  Node *rhs = find_rhs(reduction_phi); //find_rhs(acc_add, reduction_phi);
  if (rhs == NULL || rhs->req() < 2) return false;
  TRACE(MinCond, {
      tty->print_cr("Found right-hand-side N%d", rhs->_idx);
    });

  PatternInstance *_pi = match(rhs, induction_phi); //->dump();
  tty->print_cr("Before reduce");
  _pi->dump();
  tty->print_cr("After reduce");
  _pi = _pi->reduce(reduction_phi, induction_phi);
  _pi->dump();

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

  AlignInfo* align;
  bool attempt_align = false;

  {
    ResourceMark rm;

    PatternInstance *pi = match(start->in(2), induction_phi);
    if (pi == NULL)
      return false;
    // if (pi->has_alignable_load()) {
    //   attempt_align = true;
    //   align._base_addr = pi->base_addr();
    //   align._elem_bt = pi->elem_bt();
    // }
  }

  /**************************************************************
   * Vectorize IR (point of no return).
   **************************************************************/
  // if (SuperWordPolynomialMultiversion) {
  //   build_scalar_variant(phase, lpt, cl, VLEN);
  // }

  // FIXME: To avoid nesting of resource marks when calling
  // `build_loop_variants` we redo the matching, avoiding
  // GrowableArray growth within nested resource marks. Maybe look
  // over the allocation strategy used for PatternInstances?
  Node *c_term;
  {
    ResourceMark rm;
    PatternInstance *pi = match(start->in(2), induction_phi);
    assert(pi != NULL, "");
    Node_List _;
    c_term = pi->generate(phase, recurr_t, VLEN, reduction_phi, induction_phi, NULL, _,
                          lpt);
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

  int n_doublings = exact_log2(VLEN);
  while (n_doublings--) {
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
  if (cl->is_unroll_only()) return false;

  TRACE(Candidates, {
      tty->print_cr("Initial analysis of %s::%s",
                    C->method()->get_Method()->klass_name()->as_utf8(),
                    C->method()->get_Method()->name()->as_utf8());
    });

  if (!cl->stride_is_con() || cl->stride_con() != 1) return false;
  TRACE(Candidates, { tty->print_cr("  Loop is constant unit-stride"); });

  if (cl->range_checks_present()) return false;

  TRACE(Candidates, { tty->print_cr("  Loop has no range checks"); });

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

  // phase->ltree_root()->dump();
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
    cl->mark_passed_slp();
    cl->mark_was_slp();
    int n_doublings = exact_log2(8);
    while (n_doublings--) {
      cl->double_unrolled_count();
    }

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
