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

predicate stepNice(red: StepCases,conf1: configuration, conf2: configuration) {
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

predicate SameCont(conf1: configuration,conf2: configuration) {
	conf1.1 == conf2.1
}

predicate SameStore(conf1: configuration,conf2: configuration) {
	conf1.2 == conf2.2
}

predicate SameContAndStore(conf1: configuration,conf2: configuration) {
	SameCont(conf1,conf2) && SameStore(conf1,conf2)
}

predicate step(conf1: configuration, conf2: configuration) {
	match (conf1,conf2) {
		case ((CAsgn(i, a), _, s1), (SKIP, _, s2)) =>
			if (forall id: ident :: id_in_aexp(id,a) ==> id in s1) then
			&& s2 == s1[i := aeval(s1,a)]
			&& SameCont(conf1,conf2)
			else false
		case ((CSeq(c1, c2), k, _), (c', Kseq(c'', k'), _)) =>
			&& c' == c1
			&& c'' == c2
			&& k' == k
			&& SameStore(conf1,conf2)
		case ((CIf(b, c1, c2), _, s), (c, _, _)) =>
			if (forall id: ident :: id_in_bexp(id,b) ==> id in s) then
			&& if beval(s, b) then c == c1 else c == c2
			&& SameContAndStore(conf1,conf2)
			else false
		case ((CWhile(b, c), _, s), (CSkip, _, _)) =>
			if (forall id: ident :: id_in_bexp(id,b) ==> id in s) then
			&& !beval(s, b)
			&& SameContAndStore(conf1,conf2)
			else false
		case ((CWhile(b, c), k, s), (c', Kwhile(b', c'', k'), _)) =>
			if (forall id: ident :: id_in_bexp(id,b) ==> id in s) then
			&& beval(s, b)
			&& c'' == c' == c
			&& b' == b
			&& k' == k
			&& SameStore(conf1,conf2)
			else false
		case ((CSkip, Kseq(c, k), _), (c', k', _)) =>
			&& c' == c
			&& k' == k
			&& SameStore(conf1,conf2)
		case ((CSkip, Kwhile(b, c, k), _), (CWhile(b', c'), k', _)) =>
			&& b' == b
			&& c' == c
			&& k' == k
			&& SameStore(conf1,conf2)
		case _ => false
	}
}

predicate fin_reds(conf1: configuration, conf2: configuration) {
	star((c1,c2) => step(c1,c2),conf1,conf2)
}
	
predicate inf_reds(conf: configuration) {
	inf((c1,c2) => step(c1,c2),conf)
}
