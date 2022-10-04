include "Imp.dfy"
include "SemanticsCommon.dfy"
include "Semantics.dfy"	

// For now we depend on ImpNaturalSem.dfy for the semantics of expressions
// We should modularize the code more

include "ImpNaturalSem.dfy"

datatype cont =
  | Kstop
	| Kseq(com,cont)
	| Kwhile(bexp,com,cont)

type configuration = (com,cont,store)

datatype StepCases =
	| SAssign(ident,aexp,cont,store)
	| SSeq(com,com,store,cont)
	| SIf(bexp,com,com,cont,store)
	| SWhileDone(bexp,com,cont,store)
	| SWhileTrue(bexp,com,cont,store)
	| StepSkipSeq(com,cont,store)
	| StepSkipWhile(bexp,com,cont,store)

predicate step(red: StepCases,conf1: configuration, conf2: configuration) {
	match red {
		case SAssign(i,a,k,s) =>
			if (forall id: ident :: id_in_aexp(id,a) ==> id in s) then
			&& conf1 == (CAsgn(i,a),k,s[i := aeval(s,a)])
			&& conf2 == (CSkip,k,s)
			else false
		case SSeq(c1,c2,s,k) =>
			&& conf1 == (CSeq(c1, c2), k, s)
			&& conf2 == (c1, Kseq(c2, k), s)
		case SIf(b,c1,c2,k,s) =>
			if (forall id: ident :: id_in_bexp(id,b) ==> id in s) then
			&& conf1 == (CIf(b, c1, c2), k, s)
			&& conf2 == (if beval(s, b) then c1 else c2, k, s)
			else false
		case SWhileDone(b,c,k,s) =>
			&& conf1 == (CWhile(b, c), k, s)
			&& conf2 == (CSkip, k, s)
		case SWhileTrue(b,c,k,s) =>
			&& conf1 == (CWhile(b, c), k, s)
			&& conf2 == (c, Kwhile(b, c, k), s)
		case StepSkipSeq(c,k,s) =>
			&& conf1 == (CSkip, Kseq(c, k), s)
			&& conf2 == (c, k, s)
		case StepSkipWhile(b,c,k,s) =>
			&& conf1 == (CSkip, Kwhile(b, c, k), s)
			&& conf2 == (CWhile(b, c), k, s)
	}
}
