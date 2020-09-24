#ifndef SHARE_OPTO_POLYNOMIALREDUCTION_HPP
#define SHARE_OPTO_POLYNOMIALREDUCTION_HPP

#include "precompiled.hpp"
#include "utilities/globalDefinitions.hpp"

class IdealLoopTree;
class Compile;
class PhaseIdealLoop;
class PhaseIterGVN;
class Node;
class Type;
class CountedLoopNode;

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
extern const int TRACE_OPTS;

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

bool polynomial_reduction_analyze(Compile *C, PhaseIdealLoop *phase, PhaseIterGVN *igvn, IdealLoopTree *lpt);

Node *make_vector(PhaseIdealLoop *phase, Node *init, const Type *recurr_t,
                  juint vec_size, Node *control=NULL);
Node *make_vector(PhaseIdealLoop *phase, jlong init, const Type *recurr_t,
                  juint vec_size, Node *control=NULL);
void adjust_limit(CountedLoopNode *cl, PhaseIterGVN &igvn, Node *adjusted_limit);

#endif
