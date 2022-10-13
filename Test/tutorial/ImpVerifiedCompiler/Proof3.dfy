include "Proof.dfy"
include "Proof2.dfy"
	
lemma simulation_infseq_inv(C: code, impconf1: conf, machconf1: configuration)
	decreases measure(impconf1)
	requires inf(step,impconf1)
	requires match_config(C,impconf1,machconf1)
	ensures exists impconf2: conf :: exists machconf2: configuration ::
	  inf(step,impconf2)
		&& plus((c1,c2) => transition(C,c1,c2),machconf1,machconf2)
		&& match_config(C,impconf2,machconf2)
{
	
	var impconf2: conf :| step(impconf1,impconf2) && inf(step,impconf2);
	star_one_sequent<conf>(step,impconf1,impconf2);
	simulation_step(C, impconf1, impconf2, machconf1);
	var machconfi: configuration :| && (
		|| (plus((c1,c2) => transition(C,c1,c2),machconf1,machconfi))
		|| (star((c1,c2) => transition(C,c1,c2),machconf1,machconfi) && measure(impconf2) < measure(impconf1))
		)
		&& match_config(C, impconf2, machconfi);
		
		if plus((c1,c2) => transition(C,c1,c2),machconf1,machconfi) {
			
			var machconf2: configuration := machconfi;
			
		}
		else {
			
			simulation_infseq_inv(C,impconf2,machconfi);
			var impconf2: conf, machconf2: configuration :|
				inf(step,impconf2)
				&& plus((c1,c2) => transition(C,c1,c2),machconfi,machconf2)
				&& match_config(C,impconf2,machconf2);

			star_plus_trans<configuration>((c1,c2) => transition(C,c1,c2),machconf1,machconfi,machconf2);
			
		}
		
}

predicate {:opaque} X(C: code, mc: configuration) {
	exists ic: conf :: inf(step,ic) && match_config(C,ic,mc)
}
	
lemma compile_program_correct_diverging(c: com, s: store)
	requires H: inf(step,(c,Kstop,s))
	ensures machine_diverges(compile_program(c),s)
{
	var C: code := compile_program(c);
	var impconf1: conf := (c,Kstop,s);
	var machconf1: configuration := (0,[], s);
	
	assert X(C,machconf1) by {
		reveal X();
		reveal H;
		match_initial_configs(c,s);
		assert match_config(C,impconf1,machconf1);
	}

	assert always_steps((c1, c2) => transition(C,c1,c2),(mc) => X(C,mc)) by {
		reveal always_steps();
		//forall a: T :: X(a) ==> exists b: T :: plus(R,a, b) && X(b)
		forall a: configuration ensures ((mc) => X(C,mc))(a) ==> exists b: configuration :: plus((c1, c2) => transition(C,c1,c2),a, b) && ((mc) => X(C,mc))(b) {
			if ((mc) => X(C,mc))(a) {
				assert exists ic: conf :: inf(step,ic) && match_config(C,ic,a) by {
					reveal X();
				}
				var ic :| inf(step,ic) && match_config(C,ic,a);
				simulation_infseq_inv(C,ic,a);
			}
		}
	}
	

	infseq_coinduction_principle_2((c1, c2) => transition(C,c1,c2),(mc) => X(C,mc),machconf1);
	
}
