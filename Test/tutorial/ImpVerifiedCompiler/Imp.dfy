include "SyntaxCommon.dfy"

datatype aexp =
	| AConst(int)
	| AId(ident)
	| APlus(aexp, aexp)
	| AMinus(aexp, aexp)

datatype bexp =
	| BTrue
	| BFalse
	| BEq(aexp, aexp)
	| BLe(aexp, aexp)
	| BNot(bexp)
	| BAnd(bexp, bexp)

datatype com =
	| CSkip
	| CAsgn(ident, aexp)
	| CSeq(com, com)
	| CIf(bexp, com, com)
	| CWhile(bexp, com)
