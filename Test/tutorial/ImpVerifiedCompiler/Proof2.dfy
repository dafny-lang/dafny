include "Proof.dfy"

least lemma simulation_steps(C: code, impconf1: conf, impconf2: conf, machconf1: configuration)
	requires star(step,impconf1,impconf2)
	requires match_config(C, impconf1, machconf1)
	ensures exists machconf2: configuration :: star((c1,c2) => transition(C,c1,c2),machconf1,machconf2) && match_config(C, impconf2, machconf2)
{
	var tr := (c1,c2) => transition(C,c1,c2);
	if impconf1 == impconf2 {
	} else {
		var impconf_inter :| step(impconf1, impconf_inter) && star(step,impconf_inter, impconf2);
		simulation_step(C,impconf1,impconf_inter,machconf1);
		var machconf_inter :| Star(tr,machconf1,machconf_inter) && match_config(C, impconf_inter, machconf_inter);
		simulation_steps(C, impconf_inter, impconf2, machconf_inter);
		// I do not know why the skolemization needs this assert
		// It might have to do with the lambda
		assert exists machconf2: configuration :: Star((c1,c2) => transition(C,c1,c2),machconf_inter,machconf2) && match_config(C, impconf2, machconf2);
		var machconf2 :| Star((c1,c2) => transition(C,c1,c2),machconf_inter,machconf2) && match_config(C, impconf2, machconf2);
		
		star_trans_sequent<configuration>(tr,machconf1,machconf_inter,machconf2);
	}
}
	
lemma match_initial_configs(c: com, s: store)
	ensures match_config((compile_program(c)), (c, Kstop, s), (0, [], s))
{
	var C := compile_program(c);
	assert code_at(C, 0, compile_com(c)) by {
		var C1: code := [];
		var C3 := [Ihalt];
		assert C == C1 + compile_com(c) + C3;
	}
	assert C[|compile_com(c)|] == Ihalt;
	assert compile_cont(C, Kstop, |compile_com(c)|);
}

lemma compile_program_correct_terminating_2(c: com, s1: store, s2: store) 
	requires star(step,(c,Kstop,s1),(CSkip,Kstop,s2))
	ensures machine_terminates(compile_program(c),s1,s2)
{
	var C := compile_program(c);
	var impconf1 := (c,Kstop,s1);
	var impconf2 := (CSkip,Kstop,s2);
	var machconf1 := (0,[],s1);
	match_initial_configs(c,s1);
	simulation_steps(C,impconf1,impconf2,machconf1);
	// Not explicitely typing leads to annoying errors due to subset types
	var machconf1': configuration :| star((c1,c2) => transition(C,c1,c2),machconf1,machconf1')
		&& match_config(C, impconf2, machconf1');

	var pc: nat := machconf1'.0;
	assert compile_cont(C, Kstop, pc);
	compile_cont_Kstop_inv(C, pc, s2);
	
	var pc': nat :| star((c1,c2) => transition(C,c1,c2), machconf1', (pc', [], s2))
	 && pc' < |C|
	 && C[pc'] == Ihalt;

	var machconf2: configuration := (pc',[],s2);
	assert star((c1,c2) => transition(C,c1,c2), machconf1', (pc', [], s2));
	
	star_trans_sequent<configuration>((c1,c2) => transition(C,c1,c2), machconf1, machconf1',(pc', [], s2));
}

