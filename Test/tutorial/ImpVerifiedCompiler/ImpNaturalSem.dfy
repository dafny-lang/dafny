include "Imp.dfy"

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
	
least predicate cexec(s1: store, c: com, s2: store)
{
	match c
		case CSkip => s1 == s2
		case CAsgn(id,a) =>
			if (forall id: ident :: id_in_aexp(id,a) ==> id in s1) then s2 == s1[id := aeval(s1,a)] else false
		case CSeq(c1, c2) => exists si: store :: cexec(s1,c1,si) && cexec(si,c2,s2)
		case CIf(b,c1,c2) =>
			if (forall id: ident :: id_in_bexp(id,b) ==> id in s1) then 
			(if beval(s1,b) then cexec(s1,c1,s2) else cexec(s1,c2,s2))
			else false
		case CWhile(b,c) =>
			if (forall id: ident :: id_in_bexp(id,b) ==> id in s1) then 
			if beval(s1,b) then (exists si: store :: cexec(s1,c,si) && cexec(si,CWhile(b,c),s2)) else s1 == s2
			else false
}
	



