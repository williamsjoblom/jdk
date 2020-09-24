#include "opto/idiomMatch.hpp"
#include "precompiled.hpp"
#include "opto/node.hpp"
#include "opto/mulnode.hpp"
#include "opto/addnode.hpp"
#include "opto/mulnode.hpp"

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
