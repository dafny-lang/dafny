include "Sequences.dfy"

type ident = string

datatype aexp =
	| CONST(n: int)
	| VAR(x: ident)
	| PLUS(a1: aexp, a2: aexp)
	| MINUS(a1: aexp, a2: aexp)

predicate id_in_aexp(id: ident, a: aexp) {
	match a
		case CONST(n) => false
		case VAR(id') => id == id'
		case PLUS(a1, a2) => id_in_aexp(id,a1) || id_in_aexp(id,a2)
		case MINUS(a1, a2) => id_in_aexp(id,a1) || id_in_aexp(id,a2)
}
	
function aeval(s: store, a: aexp): int
	requires forall id: ident :: id_in_aexp(id,a) ==> id in s
{
	match a
		case CONST(n) => n
		case VAR(id) => s[id]
		case PLUS(a1, a2) => aeval(s,a1) + aeval(s,a2)
		case MINUS(a1, a2) => aeval(s,a1) - aeval(s,a2)
}

/* Examples of evaluation */

/* aeval_free */
	
datatype bexp =
	| TRUE
	| FALSE
	| EQUAL(a1: aexp, a2: aexp)
	| LESSEQUAL(a1: aexp, a2: aexp)
	| NOT(b1: bexp)
	| AND(b1: bexp, b2: bexp)

predicate id_in_bexp(id: ident, b: bexp) {
	match b
		case TRUE => true
		case FALSE => false
		case EQUAL(a1,a2) => id_in_aexp(id,a1) || id_in_aexp(id,a2)
		case LESSEQUAL(a1,a2) => id_in_aexp(id,a1) || id_in_aexp(id,a2)
		case NOT(b) => id_in_bexp(id,b)
		case AND(b1,b2) => id_in_bexp(id,b1) || id_in_bexp(id,b2)
			
}
	
function beval(s: store, b: bexp): bool
	requires forall id: ident :: id_in_bexp(id,b) ==> id in s
{
	match b
		case TRUE => true
		case FALSE => false
		case EQUAL(a1, a2) => aeval(s,a1) == aeval(s,a2)
		case LESSEQUAL(a1, a2) => aeval(s,a1) <= aeval(s,a2)
		case NOT(b) => ! beval(s,b)
		case AND(b1,b2) => beval(s,b1) && beval(s,b2)
}

/* Derived forms */

datatype com =
	| SKIP
	| ASSIGN(x: ident, a: aexp)
	| SEQ(c1: com, c2: com)
	| IFTHENELSE(b: bexp, c1: com, c2: com)
	| WHILE(b: bexp, c1: com)

predicate id_in_com(id: ident, c: com) {
	match c
		case SKIP => false
		case ASSIGN(id',a) => id_in_aexp(id,a) 
		case SEQ(c1, c2) => id_in_com(id,c1) || id_in_com(id,c2)
		case IFTHENELSE(b,c1,c2) => id_in_bexp(id,b) || id_in_com(id,c1) || id_in_com(id,c2)
		case WHILE(b,c) => id_in_bexp(id,b) || id_in_com(id,c)
}
	
type store = map<ident,int>

least predicate cexec(s1: store, c: com, s2: store)
{
	match c
		case SKIP => s1 == s2
		case ASSIGN(id,a) =>
			if (forall id: ident :: id_in_aexp(id,a) ==> id in s1) then s2 == s1[id := aeval(s1,a)] else false
		case SEQ(c1, c2) => exists si: store :: cexec(s1,c1,si) && cexec(si,c2,s2)
		case IFTHENELSE(b,c1,c2) =>
			if (forall id: ident :: id_in_bexp(id,b) ==> id in s1) then 
			(if beval(s1,b) then cexec(s1,c1,s2) else cexec(s1,c2,s2))
			else false
		case WHILE(b,c) =>
			if (forall id: ident :: id_in_bexp(id,b) ==> id in s1) then 
			if beval(s1,b) then (exists si: store :: cexec(s1,c,si) && cexec(si,WHILE(b,c),s2)) else s1 == s2
			else false
}

/* Missing cexec_infinite_loop and cexec_Bounded */

datatype cont =
  | Kstop
	| Kseq(c: com,k: cont)
	| Kwhile(b: bexp, c: com, k: cont)

type conf = (com,cont,store)

predicate step(conf1: conf, conf2: conf) {
	var (c1,k1,s1) := conf1;
	var (c2,k2,s2) := conf2;
	match (c1,k1) {
		case (ASSIGN(i, a), _) =>
			&& (forall id: ident :: id_in_aexp(id,a) ==> id in s1)
			&& c2 == SKIP
			&& k2 == k1
			&& s2 == s1[i := aeval(s1,a)]
		case (SEQ(c1', c1''), k) =>
			&& c2 == c1'
			&& k2 == Kseq(c1'',k)
			&& s2 == s1
		case (IFTHENELSE(b, cifso, cifnotso), _) =>
			&& (forall id: ident :: id_in_bexp(id,b) ==> id in s1)
			&& c2 == (if beval(s1, b) then cifso else cifnotso)
			&& k2 == k1
			&& s2 == s1
		case (WHILE(b, c), k) =>
			&& (forall id: ident :: id_in_bexp(id,b) ==> id in s1)
			&& c2 == (if beval(s1,b) then c else SKIP)
			&& k2 == (if beval(s1,b) then Kwhile(b,c,k) else k1)
			&& s2 == s1
		case (SKIP, Kseq(c, k)) =>
			&& c2 == c
			&& k2 == k
			&& s2 == s1
		case (SKIP, Kwhile(b, c, k)) =>
			&& c2 == WHILE(b,c)
			&& k2 == k
			&& s2 == s1
		case _ => false
	}
}

/*
predicate fin_reds(conf1: conf, conf2: conf) {
	star((c1,c2) => step(c1,c2),conf1,conf2)
}
	
predicate inf_reds(conf: conf) {
	infseq((c1,c2) => step(c1,c2),conf)
}
*/
