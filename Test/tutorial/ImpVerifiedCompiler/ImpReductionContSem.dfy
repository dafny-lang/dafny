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

type conf = (com,cont,store)

predicate step(conf1: conf, conf2: conf) {
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

predicate fin_reds(conf1: conf, conf2: conf) {
	star((c1,c2) => step(c1,c2),conf1,conf2)
}
	
predicate inf_reds(conf: conf) {
	inf((c1,c2) => step(c1,c2),conf)
}
