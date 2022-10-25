include "SequencesTest.dfy"

module Z {

	type ident = string

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

	datatype cont =
		| Kstop
		| Kseq(com,cont)
		| Kwhile(bexp,com,cont)
		
	type store = map<ident,int>

}
	
module X refines SEQUENCES {

	import opened Z
	
	type T(!new) = (com,cont,store) 

}

import opened Z
	
type conf = X.T
	
predicate id_in_aexp(id: ident, a: aexp) {
	match a
		case AConst(n) => false
		case AId(id') => id == id'
		case APlus(a1, a2) => id_in_aexp(id,a1) || id_in_aexp(id,a2)
		case AMinus(a1, a2) => id_in_aexp(id,a1) || id_in_aexp(id,a2)
}
	
function aeval(s: store, a: aexp): int
	requires forall id: ident :: id_in_aexp(id,a) ==> id in s
{
	match a
		case AConst(n) => n
		case AId(id) => s[id]
		case APlus(a1, a2) => aeval(s,a1) + aeval(s,a2)
		case AMinus(a1, a2) => aeval(s,a1) - aeval(s,a2)
}
	
predicate id_in_bexp(id: ident, b: bexp) {
	match b
		case BTrue => true
		case BFalse => false
		case BEq(a1,a2) => id_in_aexp(id,a1) || id_in_aexp(id,a2)
		case BLe(a1,a2) => id_in_aexp(id,a1) || id_in_aexp(id,a2)
		case BNot(b) => id_in_bexp(id,b)
		case BAnd(b1,b2) => id_in_bexp(id,b1) || id_in_bexp(id,b2)
			
}
	
function beval(s: store, b: bexp): bool
	requires forall id: ident :: id_in_bexp(id,b) ==> id in s
{
	match b
		case BTrue => true
		case BFalse => false
		case BEq(a1, a2) => aeval(s,a1) == aeval(s,a2)
		case BLe(a1, a2) => aeval(s,a1) <= aeval(s,a2)
		case BNot(b) => ! beval(s,b)
		case BAnd(b1,b2) => beval(s,b1) && beval(s,b2)
}
	
predicate id_in_com(id: ident, c: com) {
	match c
		case CSkip => false
		case CAsgn(id',a) => id_in_aexp(id,a) 
		case CSeq(c1, c2) => id_in_com(id,c1) || id_in_com(id,c2)
		case CIf(b,c1,c2) => id_in_bexp(id,b) || id_in_com(id,c1) || id_in_com(id,c2)
		case CWhile(b,c) => id_in_bexp(id,b) || id_in_com(id,c)
}



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
			&& c2 == c1'
			&& k2 == Kseq(c1'',k)
			&& s2 == s1
		case (CIf(b, cifso, cifnotso), _) =>
			&& (forall id: ident :: id_in_bexp(id,b) ==> id in s1)
			&& c2 == (if beval(s1, b) then cifso else cifnotso)
			&& k2 == k1
			&& s2 == s1
		case (CWhile(b, c), k) =>
			&& (forall id: ident :: id_in_bexp(id,b) ==> id in s1)
			&& c2 == (if beval(s1,b) then c else CSkip)
			&& k2 == (if beval(s1,b) then Kwhile(b,c,k) else k1)
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
	X.star((c1,c2) => step(c1,c2),conf1,conf2)
}
	
predicate inf_reds(conf: conf) {
	X.inf((c1,c2) => step(c1,c2),conf)
}


