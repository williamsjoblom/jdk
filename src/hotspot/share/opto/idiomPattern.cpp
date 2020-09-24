#include "opto/idiomPattern.hpp"

#include "precompiled.hpp"
#include "opto/polynomialReduction.hpp"
#include "opto/node.hpp"
#include "opto/addnode.hpp"
#include "opto/memnode.hpp"
#include "opto/mulnode.hpp"
#include "opto/connode.hpp"
#include "opto/type.hpp"
#include "opto/vectornode.hpp"
#include "opto/callnode.hpp"
#include "opto/output.hpp"
#include "opto/castnode.hpp"
#include "opto/convertnode.hpp"

/****************************************************************
 * Reduce.
 ****************************************************************/
PatternInstance *ArrayStorePattern::reduce(Node *reduction_phi, Node *iv) {
  //_access = _access->reduce(reduction_phi, iv);
  _stored_value = _stored_value->reduce(reduction_phi, iv);

  if (PatternInstance *p = PrefixSumPattern::make(this))
    return p;

  return this;
}

PatternInstance *BinOpPattern::reduce(Node *reduction_phi, Node *iv) {
  _lhs = _lhs->reduce(reduction_phi, iv);
  _rhs = _rhs->reduce(reduction_phi, iv);

  if (PatternInstance *p = PrefixBinOpPattern::make(this)) return p;

  return this;
}

/****************************************************************
 * Reduction factories.
 ****************************************************************/

PrefixBinOpPattern *PrefixBinOpPattern::make(BinOpPattern *binop) {
  if (binop->_lhs->op() == ArrayLoad && binop->_rhs->op() == ArrayLoad &&
      binop->_opcode == Op_AddI) {
    ArrayLoadPattern *lhs = static_cast<ArrayLoadPattern *>(binop->_lhs);
    ArrayLoadPattern *rhs = static_cast<ArrayLoadPattern *>(binop->_rhs);

    ArrayLoadPattern *prefix;
    ArrayLoadPattern *c;

    if (lhs->_access->_offset == NULL && rhs->_access->_offset == NULL) {
      return NULL;
    } else if (lhs->_access->_offset == NULL && rhs->_access->_offset != NULL) {
      prefix = rhs;
      c = lhs;
    } else if (rhs->_access->_offset == NULL && lhs->_access->_offset != NULL) {
      prefix = lhs;
      c = rhs;
    } else {
      return NULL;
    }

    bool prefix_has_decremented_offset =
        prefix->_access->_offset->is_Con() &&
        prefix->_access->_offset->get_int() == -1;
    if (!prefix_has_decremented_offset)
      return NULL;

    PrefixBinOpPattern *p = new PrefixBinOpPattern;
    p->_prefix = prefix;
    p->_c = c;
    return p;
  }

  return NULL;
}

Node *ArrayLoadPattern::generate(PhaseIdealLoop *phase, const Type *recurr_t, uint vlen,
                         Node *reduction_phi, Node *iv) {
  assert(_access->_offset == NULL, "not implemented");
  BasicType recurr_bt = recurr_t->array_element_basic_type();

  LoadNode *load = _access->_load->as_Load();
  BasicType load_type = _access->_bt;
  BasicType elem_type = load->memory_type();

  TRACE(Rewrite, {
    tty->print_cr("load: %s, elem: %s, recur: %s", type2name(load_type),
                  type2name(elem_type), type2name(recurr_bt));
  });

  // No implicit cast.
  if (elem_type == recurr_bt) {
    Node *arr = LoadVectorNode::make(
        _access->_load->Opcode(), _access->_load->in(LoadNode::Control), _access->_memory,
        _access->_load->in(LoadNode::Address), _access->_load->adr_type(), vlen, recurr_bt);
    phase->igvn().register_new_node_with_optimizer(arr, NULL);
    return arr;
  } else {
    Node *arr = LoadVectorNode::make_promotion(
        _access->_load->Opcode(), _access->_load->in(LoadNode::Control), _access->_memory,
        _access->_load->in(LoadNode::Address), _access->_load->adr_type(), vlen, recurr_bt);
    phase->igvn().register_new_node_with_optimizer(arr, NULL);
    return arr;
  }

  ShouldNotReachHere();
  return NULL;
}

void ArrayLoadPattern::dump(int indent) {
  print_indent(indent);
  tty->print("ARRAYLOAD[N%d", _access->_index->_idx);
  if (_access->_offset != NULL) {
    if (_access->_offset->Opcode() == Op_ConI)
      tty->print_cr(" + %d]", _access->_offset->get_int());
    else
      tty->print_cr(" + N%d]", _access->_offset->_idx);
  } else {
    tty->print_cr("]");
  }
}

void ArrayStorePattern::dump(int indent) {
  print_indent(indent);
  tty->print("ARRAYSTORE[N%d", _access->_index->_idx);
  if (_access->_offset != NULL) {
    if (_access->_offset->Opcode() == Op_ConI)
      tty->print_cr(" + %d]", _access->_offset->get_int());
    else
      tty->print_cr(" + N%d]", _access->_offset->_idx);
  } else {
    tty->print_cr("]");
  }

  _stored_value->dump(indent + 1);
}

/****************************************************************
 * Generate.
 ****************************************************************/

Node *ScalarPattern::generate(PhaseIdealLoop *phase, const Type *recurr_t, uint vlen,
                              Node *reduction_phi, Node *iv) {
  return make_vector(phase, _scalar, recurr_t, vlen);
}

Node *BinOpPattern::generate(PhaseIdealLoop *phase, const Type *recurr_t, uint vlen,
                             Node *reduction_phi, Node *iv) {
  Node *lhs = _lhs->generate(phase, recurr_t, vlen, reduction_phi, iv);
  Node *rhs = _rhs->generate(phase, recurr_t, vlen, reduction_phi, iv);

  // TODO: Should we use `_bt` or `recurr_t->array_element_basic_type()` here?
  Node *result = VectorNode::make(_opcode, lhs, rhs, vlen, _bt);
  phase->igvn().register_new_node_with_optimizer(result);
  return result;
}


Node *LShiftPattern::generate(PhaseIdealLoop *phase, const Type *recurr_t, uint vlen,
                              Node *reduction_phi, Node *iv) {
  assert(_opcode == Op_LShiftI, "sanity");
  assert(_rhs->result()->is_Con(), "not implemented");

  BasicType recurr_bt = recurr_t->array_element_basic_type();
  Node *lhs = _lhs->generate(phase, recurr_t, vlen, reduction_phi, iv);

  Node *multiplier = phase->igvn().intcon(1 << _rhs->result()->get_int());
  // TODO: `make_vector` needs control dependency on loop entry
  // control, without this dependency the vector initialization may
  // be scheduled before the deciding on vector/scalar loop.
  Node *result = VectorNode::make(
      Op_MulI, lhs, make_vector(phase, multiplier, recurr_t, vlen), vlen,
      recurr_bt);
  // new MulVINode(lhs, make_vector(phase, multiplier, vlen),
  // TypeVect::make(recurr_bt, vlen));
  phase->igvn().register_new_node_with_optimizer(result);
  return result;
}

Node *PrefixSumPattern::generate(PhaseIdealLoop *phase, const Type *recurr_t, uint vlen,
                                 Node *reduction_phi, Node *iv) {
  PhaseIterGVN& igvn = phase->igvn();

  const BasicType recurr_bt = recurr_t->array_element_basic_type();
  const int ELEM_SZ = type2aelembytes(recurr_bt);

  Node *initial_prefix = VectorNode::scalar2vector(NULL, vlen, recurr_t);
  PhiNode *prefix_phi = PhiNode::make(iv->in(PhiNode::Region), initial_prefix);

  Node *c_load = stored_value()->_c->generate(phase, recurr_t, vlen, reduction_phi, iv);
  Node *last_add = c_load;
  // Hillis and Steele parallel prefix sum algorithm:
  for (uint i = 1; i < vlen; i *= 2) {
    Node *shift = new ElemLShiftVNode(last_add, igvn.intcon(ELEM_SZ*i),
                                      TypeVect::make(recurr_bt, vlen));
    Node *add = VectorNode::make(Op_AddI, last_add, shift, vlen, recurr_bt);
    igvn.register_new_node_with_optimizer(shift);
    igvn.register_new_node_with_optimizer(add);
    last_add = add;
  }

  Node *prev_prefix_add = VectorNode::make(Op_AddI, prefix_phi, last_add, vlen, recurr_bt);
  igvn.register_new_node_with_optimizer(prev_prefix_add);


  // NOTE: ExtractI nodes are not currently implemented except for
  // when used in combination with a ReplicateI node.
  Node *extract_last = new ExtractINode(prev_prefix_add, igvn.intcon(3));
  igvn.register_new_node_with_optimizer(extract_last);
  Node *repl_last = new ReplicateINode(extract_last, TypeVect::make(recurr_bt, vlen));
  igvn.register_new_node_with_optimizer(repl_last);
  prefix_phi->set_req(2, repl_last);

  Node *store = this->_access->_load;
  assert(store->is_Store(), "sanity");
  StoreVectorNode *storev = StoreVectorNode::make(store->Opcode(),
                                                  store->in(MemNode::Control),
                                                  store->in(MemNode::Memory),
                                                  store->in(MemNode::Address),
                                                  store->adr_type(), prev_prefix_add, vlen);
  return storev;
}


/****************************************************************
 * Matching.
 ****************************************************************/

ArrayAccessPattern *match_array_access(Node *start, Node *idx,
                                     NodePred start_predicate,
                                     bool allow_offset) {
  ArrayAccessPattern *result = new ArrayAccessPattern();

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
    (start_predicate,
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

    assert(result->_load_ctrl->isa_Proj(), "sanity");
    return result;
  } else {
    TRACE(Match, {
        tty->print_cr("  origin array_read");
      });
    return NULL;
  }
}

ArrayLoadPattern *match_array_read(Node *start, Node *idx,
                                   bool allow_offset) {
  ArrayAccessPattern *p = match_array_access(start, idx, is_primitive_load, allow_offset);
  if (p == NULL) return NULL;
  ArrayLoadPattern *lp = new ArrayLoadPattern();
  lp->_access = p;
  return lp;
}

ArrayStorePattern *match_array_store(Node *start, Node *idx,
                                     bool allow_offset) {
  ArrayAccessPattern *p = match_array_access(start, idx, is_primitive_store, allow_offset);
  if (p == NULL) return NULL;
  PatternInstance *stored_value = match(start->in(MemNode::ValueIn), idx);
  if (stored_value == NULL) return NULL;

  ArrayStorePattern *sp = new ArrayStorePattern(p, stored_value);
  return sp;
}

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
  if (start->Opcode() == Op_ConI || start->Opcode() == Op_ConF ||
      start->Opcode() == Op_ConD) {
    ScalarPattern *p = new ScalarPattern();
    p->_scalar = start;
    return p;
  } else if (start->Opcode() == Op_Phi) {
    ScalarPattern *p = new ScalarPattern();
    p->_scalar = start;
    return p;
  } else {
    return NULL;
  }
}

// Start is reduction phi->in(2).
PatternInstance *match_prefix_sum(Node *start, Node *iv) {
  PatternInstance *store = match_array_store(start, iv, true);

  return NULL;
}

PatternInstance *match(Node *start, Node *iv) {
  PatternInstance *pi;
  if (pi = match_array_read(start, iv, true))
    return pi;
  if (pi = match_array_store(start, iv))
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
