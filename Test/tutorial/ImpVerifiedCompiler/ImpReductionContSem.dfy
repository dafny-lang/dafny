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
			&& (forall id: ident :: id_in_aexp(id,a) ==> id in s)
			&& conf1 == (CAsgn(i,a),k,s[i := aeval(s,a)])
			&& conf2 == (CSkip,k,s)
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
	var (c1,k1,s1) := conf1;
	var (c2,k2,s2) := conf2;
	match (c1,k1) {
		case (CAsgn(i, a), _) =>
			&& (forall id: ident :: id_in_aexp(id,a) ==> id in s1)
			&& c2 == CSkip
			&& k2 == k1
			&& s2 == s1[i := aeval(s1,a)]
		case (CSeq(c1', c1''), k) =>
			&& c2 == c1''
			&& k2 == Kseq(c1'',k)
			&& s2 == s1
		case (CIf(b, cifso, cifnotso), _) =>
			&& (forall id: ident :: id_in_bexp(id,b) ==> id in s1)
			&& c2 == (if beval(s1, b) then cifso else cifnotso)
			&& k2 == k1
			&& s2 == s1
		case (CWhile(b, c), _) =>
			&& (forall id: ident :: id_in_bexp(id,b) ==> id in s1)
			&& !beval(s1, b)
			&& c2 == CSkip
			&& k2 == k1
			&& s2 == s1
		case (CWhile(b, c), k) =>
			(forall id: ident :: id_in_bexp(id,b) ==> id in s1)
			&& beval(s1, b)
			&& c2 == c
			&& k2 == Kwhile(b,c,k)
			&& s2 == s1
		case (CSkip, Kseq(c, k)) =>
			&& c2 == c
			&& k2 == k
			&& s2 == s1
		case (CSkip, Kwhile(b, c, k)) =>
			&& c2 == CWhile(b,c)
			&& k2 == k
			&& s2 == s1
		case _ => false
	}
}

predicate fin_reds(conf1: configuration, conf2: configuration) {
	star((c1,c2) => step(c1,c2),conf1,conf2)
}
	
predicate inf_reds(conf: configuration) {
	inf((c1,c2) => step(c1,c2),conf)
}
