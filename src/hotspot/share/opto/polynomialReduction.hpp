#ifndef SHARE_OPTO_POLYNOMIALREDUCTION_HPP
#define SHARE_OPTO_POLYNOMIALREDUCTION_HPP

class IdealLoopTree;
class Compile;
class PhaseIdealLoop;
class PhaseIterGVN;

bool polynomial_reduction_analyze(Compile *C, PhaseIdealLoop *phase, PhaseIterGVN *igvn, IdealLoopTree *lpt);

#endif
