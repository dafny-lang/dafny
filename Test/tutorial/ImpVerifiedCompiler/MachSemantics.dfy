include "Mach.dfy"
include "SemanticsCommon.dfy"
include "Semantics.dfy"
	
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

predicate machine_diverges(C: code, s_init: store) {
	inf((c1,c2) => transition(C,c1,c2),(0,[],s_init))
}
