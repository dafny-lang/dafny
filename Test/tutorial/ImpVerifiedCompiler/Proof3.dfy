include "Proof.dfy"
include "Proof2.dfy"
	
lemma simulation_infseq_inv(C: code, impconf1: conf, machconf1: configuration)
	requires inf(step,impconf1)
	requires match_config(C,impconf1,machconf1)
	ensures exists impconf2: conf :: exists machconf2: configuration ::
	  inf(step,impconf2)
		&& plus((c1,c2) => transition(C,c1,c2),machconf1,machconf2)
		&& match_config(C,impconf2,machconf2)
{
	var impconf2: conf :| step(impconf1,impconf2) && inf(step,impconf2);
	star_one_sequent<conf>(step,impconf1,impconf2);
	simulation_steps(C, impconf1, impconf2, machconf1);
	var machconf2: configuration :| star((c1,c2) => transition(C,c1,c2),machconf1,machconf2) && match_config(C, impconf2, machconf2);

	assume plus((c1,c2) => transition(C,c1,c2),machconf1,machconf2);
}

lemma compile_program_correct_diverging(c: com, s: store)
	requires inf(step,(c,Kstop,s))
	ensures machine_diverges(compile_program(c),s)
{
	var C: code := compile_program(c);
	var impconf1: conf := (c,Kstop,s);
	var machconf1: configuration := (0,[], s);
	match_initial_configs(c,s);
	var X: configuration -> bool := (mc: configuration) => exists ic: conf :: inf(step,ic) && match_config(C,ic,mc);
	assert X(machconf1);
	simulation_infseq_inv(C,impconf1,machconf1);
	assume (forall a: configuration :: X(a) ==> exists b: configuration :: plus((c1,c2) => transition(C,c1,c2),a, b) && X(b));
	infseq_coinduction_principle_2((c1,c2) => transition(C,c1,c2),X,machconf1);
}
