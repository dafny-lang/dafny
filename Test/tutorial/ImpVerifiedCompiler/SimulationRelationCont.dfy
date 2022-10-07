include "SimulationRelation.dfy"
include "ImpReductionContSem.dfy"
include "Mach.dfy"
include "MachSemantics.dfy"
include "Compiler.dfy"

least predicate compile_cont(C: code, k: cont, pc: nat) {
	if ! (pc < |C|) then false else
	match (k,C[pc]) {
		case (Kstop,Ihalt) => true
		case (Kseq(c,k),_) =>
			var pc' := pc + |compile_com(c)|;
			&& code_at(C, pc, (compile_com(c)))
			&& compile_cont(C, k, pc')
		case (Kwhile(b,c,k),Ibranch(ofs)) =>
			var pc' := pc + 1 + ofs;
			var pc'' := pc' + |compile_com(CWhile(b, c))|;
			&& pc' > 0
			&& pc'' > 0	
      && code_at(C, pc', (compile_com(CWhile(b, c)))) 
      && compile_cont(C, k, pc'')
		case (_,Ibranch(ofs)) =>
			var pc' := pc + 1 + ofs;
			&& pc' > 0
      && compile_cont(C, k, pc')
		case _ => false
	}
	
}

predicate match_config(C: code, hl: conf, ll:configuration) {
	var (c,k,s) := hl;
	var (pc,stk,str) := ll;
	&& code_at(C, pc, compile_com(c))
	&& compile_cont(C, k, pc + |compile_com(c)|)
	&& stk == []
	&& str == s
}

lemma match_config_skip(C: code, k: cont, s: store, pc: nat)
	requires compile_cont(C, k, pc)
	ensures match_config(C, (CSkip, k, s), (pc, [], s))
{

	assert pc < |C|;
	var Cleft := C[..pc];
	assert |Cleft| == pc;
	var Cright := C[pc..];
	assert C == Cleft + Cright;
	var Cmid := [];
	assert C == Cleft + Cmid + Cright;

}

