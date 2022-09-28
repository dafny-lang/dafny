include "Identifier.dfy"
include "Smallstep.dfy"

type offset = int

datatype instruction =
  | Iconst(int)
  | Ivar(ident)
  | Isetvar(string)
  | Iadd
	| Iopp
  | Ibranch(offset)
  | Ibeq(offset,offset)
  | Ible(offset,offset)
  | Ihalt

type code = seq<instruction>

type stack = seq<int>
	
type configuration = (nat,stack,store)

predicate transition(c: code, conf1: configuration, conf2: configuration) {
	var (pc1,stk1,st1) := conf1;
	var (pc2,stk2,st2) := conf2;
	if ! (pc1 < |c|) then false else
		match c[pc1]
			case Iconst(n) =>
				&& pc2 == pc1 + 1
				&& stk2 == [n] + stk1
				&& st1 == st2
			case Ivar(id) =>
				&& pc2 == pc1 + 1
				&& (id in st1) && (stk2 == [st1[id]] + stk1)
				&& st1 == st2
			case Isetvar(id) =>
				&& pc2 == pc1 + 1
				&& |stk1| > 0 && stk2 == stk1[1..]
				&& st2 == st1[id := stk1[0]]  
			case Iadd => 
				&& pc2 == pc1 + 1
				&& |stk1| > 1 && stk2 == [stk1[0] + stk1[1]] + stk1[2..]
				&& st1 == st2
			case Iopp => 
				&& pc2 == pc1 + 1
				&& |stk1| > 0 && stk2 == [-stk1[0]] + stk1[1..]
				&& st1 == st2
			case Ibranch(ofs) =>
				&& pc2 == pc1 + 1 + ofs
				&& stk2 == stk1
				&& st1 == st2
			case Ibeq(ofs1,ofs2) =>
				&& |stk1| > 1 && pc2 == pc1 + 1 + (if stk1[0] == stk1[1] then ofs1 else ofs2)
				&& stk2 == stk1[2..]
				&& st1 == st2
			case Ible(ofs1,ofs2) =>
				&& |stk1| > 1 && pc2 == pc1 + 1 + (if stk1[1] <= stk1[0] then ofs1 else ofs2)
				&& stk2 == stk1[2..]
				&& st1 == st2
			case Ihalt => false	
}

predicate transitions(C: code, conf1: configuration, conf2: configuration) {
	star((c1,c2) => transition(C,c1,c2),conf1,conf2)
}

predicate machine_terminates(C: code, s_init: store, s_final: store) {
	exists pc: nat :: transitions(C,(0,[],s_init),(pc,[],s_final)) && pc < |C| && C[pc] == Ihalt
}

predicate code_at(C: code, pc: nat, C2: code) {
	exists C1, C3: code :: C == C1 + C2 + C3 && |C1| == pc
}

lemma code_at_app_left(C: code, pc: nat, C1: code, C2: code)
	requires code_at(C,pc,C1 + C2)
	ensures code_at(C,pc,C1)
{
	var C0, C3 :| C == C0 + (C1 + C2) + C3 && |C0| == pc;
	assert C == C0 + C1 + (C2 + C3) && |C0| == pc;
}

lemma code_at_app_right(C: code, pc: nat, C1: code, C2: code)
	requires code_at(C,pc,C1 + C2)
	ensures code_at(C,pc + |C1|,C2)
{
	var C0, C3 :| C == C0 + (C1 + C2) + C3 && |C0| == pc;
	assert C == (C0 + C1) + C2 + C3 && |C0 + C1| == pc + |C1|;
}

lemma resolve_code_at()
	ensures forall C: code :: forall pc: nat :: forall C1, C2: code :: code_at(C,pc,C1 + C2) ==> code_at(C,pc,C1)
	ensures forall C: code :: forall pc: nat :: forall C1, C2: code :: code_at(C,pc,C1 + C2) ==> code_at(C,pc + |C1|,C2)
{
	forall C, pc, C1, C2 ensures code_at(C,pc,C1 + C2) ==> code_at(C,pc,C1) {
		if code_at(C,pc,C1 + C2) {
			code_at_app_left(C,pc,C1,C2);
		}
	}
	// Surprisingly, in what follows, if we do not provide the type annotation on pc,
	// then Dafny fails to recognize that pc is a nat
	forall C, pc: nat, C1, C2 ensures code_at(C,pc,C1 + C2) ==> code_at(C,pc + |C1|,C2) {
		if code_at(C,pc,C1 + C2) {
			code_at_app_right(C,pc,C1,C2);
		}
	}
}
