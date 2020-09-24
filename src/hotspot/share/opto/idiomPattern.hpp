#ifndef SHARE_OPTO_IDIOMPATTERN_HPP
#define SHARE_OPTO_IDIOMPATTERN_HPP


#include "precompiled.hpp"
#include "polynomialReduction.hpp"
#include "memory/allocation.hpp"
#include "opto/node.hpp"
#include "opto/connode.hpp"
#include "opto/loopnode.hpp"
#include "opto/idiomMatch.hpp"
#include "opto/idiomPattern.hpp"

struct PatternInstance : ResourceObj {
  enum {
    ArrayAccess,
    ArrayLoad,
    ArrayStore,
    BinOp,
    PrefixBinOp,
    Scalar,

    PrefixSum,
  };

  /**************************************************************
   * Pure virtuals.
   **************************************************************/
  virtual int op() = 0;
  virtual void dump(int indent=0) = 0;


  // Generate Node.
  virtual Node *generate(PhaseIdealLoop *phase, const Type *recurr_t,
                         uint vlen, Node *reduction_phi, Node *iv){
    ShouldNotCallThis();
    return NULL;
  }
  virtual Node *result() { ShouldNotCallThis(); return NULL; };

  virtual bool has_alignable_load() { return false; }
  virtual int memory_stride() { return 0; }
  virtual BasicType elem_bt() { ShouldNotCallThis(); return T_ILLEGAL; }
  virtual Node *base_addr() { ShouldNotCallThis(); return NULL; };

  static void print_indent(int indent) {
    while (indent--) tty->print(" ");
  }

  // TODO: make pure virtual.
  virtual PatternInstance *reduce(Node *reduction_phi, Node *iv) { return this; };
};

/****************************************************************
 * Primitive patterns.
 ****************************************************************/
struct ArrayAccessPattern : PatternInstance {
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

  virtual int op() { return ArrayAccess; }
  virtual Node *result() { return _load; }
  virtual bool has_alignable_load() { return true; }
  virtual int memory_stride() { return _elem_byte_size; }
  virtual BasicType elem_bt() { return _load->as_Load()->memory_type(); }
  virtual Node *base_addr() { return _array_ptr; }
  virtual void dump(int indent = 0) { ShouldNotCallThis(); }
};

// Array load pattern instance.
struct ArrayLoadPattern : PatternInstance {
  ArrayAccessPattern *_access;
  virtual int op() { return ArrayLoad; }
  virtual Node *generate(PhaseIdealLoop *phase, const Type *recurr_t, uint vlen,
                         Node *reduction_phi, Node *iv);
  virtual Node *result() { return _access->result(); }
  virtual bool has_alignable_load() { return true; }
  virtual int memory_stride() { return _access->memory_stride(); }
  virtual BasicType elem_bt() { return _access->elem_bt(); }
  virtual Node *base_addr() { return _access->base_addr(); }
  virtual void dump(int indent=0);
};

struct ArrayStorePattern : PatternInstance {
  ArrayAccessPattern *_access;
  PatternInstance *_stored_value;

  ArrayStorePattern(ArrayAccessPattern *access, PatternInstance *stored_value)
    : _access(access), _stored_value(stored_value) {}

  virtual int op() { return ArrayStore; }
  virtual Node *result() { return _access->result(); }
  virtual bool has_alignable_load() { return true; }
  virtual int memory_stride() { return _access->memory_stride(); }
  virtual BasicType elem_bt() { return _access->elem_bt(); }
  virtual Node *base_addr() { return _access->base_addr(); }
  virtual void dump(int indent=0);

  virtual PatternInstance *reduce(Node *reduction_phi, Node *iv);
};

struct ScalarPattern : PatternInstance {
  Node *_scalar;

  virtual int op() { return Scalar; }
  virtual Node *generate(PhaseIdealLoop *phase, const Type *recurr_t, uint vlen,
                         Node *reduction_phi, Node *iv);

  virtual Node *result() {
    return _scalar;
  }

  virtual bool has_alignable_load() { return false; }
  virtual Node *base_addr() { ShouldNotCallThis(); return NULL; }
  virtual void dump(int indent = 0) {
    print_indent(indent);
    tty->print_cr("SCALAR");
  }
};

struct BinOpPattern : PatternInstance {
  int _opcode;
  PatternInstance *_lhs, *_rhs;
  BasicType _bt;

  virtual int op() { return BinOp; }

  virtual Node *generate(PhaseIdealLoop *phase, const Type *recurr_t, uint vlen,
                         Node *reduction_phi, Node *iv);

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

  virtual void dump(int indent = 0) {
    print_indent(indent);
    tty->print_cr("BINOP");
    _lhs->dump(indent + 1);
    _rhs->dump(indent + 1);
  }

  virtual PatternInstance *reduce(Node *reduction_phi, Node *iv);
};

/****************************************************************
 * Higer-order patterns.
 ****************************************************************/
struct PrefixBinOpPattern : PatternInstance {
  PatternInstance *_prefix;
  PatternInstance *_c;

  virtual int op() { return PrefixBinOp; }
  virtual void dump(int indent) {
    print_indent(indent);
    tty->print("PrefixBinOp");
    _prefix->dump(indent + 1);
    _c->dump(indent + 1);
  }

  static PrefixBinOpPattern *make(BinOpPattern *binop);
};


struct PrefixSumPattern : ArrayStorePattern {
  PrefixSumPattern(ArrayAccessPattern *access, PatternInstance *stored_value)
    : ArrayStorePattern(access, stored_value) {}

  PrefixBinOpPattern *stored_value() {
    assert(_stored_value->op() == PrefixBinOp,
           "reducing down to this node shall require"
           "the stored value to be a PrefixBinOp");
    return static_cast<PrefixBinOpPattern*>(_stored_value);
  }

  virtual int op() { return PrefixSum; }
  virtual Node *result() { return _access->result(); }
  virtual bool has_alignable_load() { return true; }
  virtual int memory_stride() { return _access->memory_stride(); }
  virtual BasicType elem_bt() { return _access->elem_bt(); }
  virtual Node *base_addr() { return _access->base_addr(); }
  virtual void dump(int indent = 0) {
    print_indent(indent);
    tty->print_cr("PREFIXSUM");
  }

  virtual Node *generate(PhaseIdealLoop *phase, const Type *recurr_t, uint vlen,
                         Node *reduction_phi, Node *iv);

  static PrefixSumPattern *make(ArrayStorePattern *p) {
    if (p->_stored_value->op() != PrefixBinOp) return NULL;
    return new PrefixSumPattern(p->_access, p->_stored_value);
  }
};


struct LShiftPattern : BinOpPattern {
  virtual Node *generate(PhaseIdealLoop *phase, const Type *recurr_t, uint vlen,
                         Node *reduction_phi, Node *iv);
};

// Reduction on the form:
//   x = N*x + C
// (N: constant, C: expression not depending on x)
struct ReductionPattern : PatternInstance {
  Node *_root; // op_reduce = _root->Opcode();
  PatternInstance* _c;
  JavaValue _n;
};


/****************************************************************
 * Matching.
 ****************************************************************/
ArrayAccessPattern *match_array_access(Node *start, Node *idx,
                                     NodePred start_predicate,
                                     bool allow_offset=false);
ArrayLoadPattern *match_array_read(Node *start, Node *idx,
                                   bool allow_offset = false);
ArrayStorePattern *match_array_store(Node *start, Node *idx,
                                    bool allow_offset = false);
PatternInstance *match_binop(Node *start, Node *iv);
PatternInstance *match_scalar(Node *start);
PatternInstance *match_prefix_sum(Node *start, Node *iv);
PatternInstance *match(Node *start, Node *iv);

#endif
