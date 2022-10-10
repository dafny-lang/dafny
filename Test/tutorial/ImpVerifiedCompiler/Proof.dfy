include "SimulationRelationCont.dfy"
include "ImpReductionContSem.dfy"
include "MachSemantics.dfy"	
include "SemanticsProperties.dfy"
include "CompileAexpCorrect.dfy"
include "CompileBexpCorrect.dfy"

function com_size(c: com): nat {

	match c {
		case CSkip => 1
		case CAsgn(_,_) => 1 
		case CSeq(c1,c2) => com_size(c1) + com_size(c2) + 1
		case CIf(b,c1,c2) => com_size(c1) + com_size(c2) + 1 
		case CWhile(b,c) => com_size(c) + 1 
	}

}

function cont_size(k: cont): nat {

	match k {
		case Kstop => 0
		case Kseq(c,k) => com_size(c) + cont_size(k)
		case Kwhile(b,c,k) => cont_size(k)
	}

}

function measure(impconf: conf): nat {
	com_size(impconf.0) + cont_size(impconf.1)
}

lemma {:axiom} bypass() ensures false

lemma simulation_step(C: code, impconf1: conf, impconf2: conf, machconf1: configuration)
	requires step(impconf1,impconf2)
	requires match_config(C, impconf1, machconf1)
	ensures exists machconf2: configuration ::
	&& (
	|| (plus((c1,c2) => transition(C,c1,c2),machconf1,machconf2))
	|| (star((c1,c2) => transition(C,c1,c2),machconf1,machconf2) && measure(impconf2) < measure(impconf1))
	)
	&& match_config(C, impconf2, machconf2)
{
	match (impconf1.0,impconf1.1) {
		
		case (CAsgn(i, a), _) => {
			assert {:split_here} true;
			var tr := (c1,c2) => transition(C,c1,c2);
			
			var (c1,k1,s1) := impconf1;
			var (c2,k2,s2) := impconf2;
			var (pc1,stk1,str1) := machconf1;

			assert (c2,k2,s2) == (CSkip,k1,s1[i := aeval(s1,a)]);

			var chunk := compile_aexp(a) + [Isetvar(i)];
			assert code_at(C, pc1, chunk);
			assert compile_cont(C, k1, pc1 + |chunk|);
			assert (pc1,stk1,str1) == (pc1,[],s1);

			var machconf2: configuration := (pc1 + |chunk|,[],s2);
			var (pc2,stk2,str2) := machconf2;

			assert star(tr,machconf1,machconf2) by {
				
				var machconf1': configuration := (pc1 + |compile_aexp(a)|, [aeval(s1,a)] + stk1, str1);
				assert code_at(C, pc1, compile_aexp(a)) by { resolve_code_at(); }
				assert transitions(C,machconf1,machconf1') by { compile_aexp_correct_gen(); }
				assert star(tr,machconf1,machconf1');

				assert transition(C,machconf1',machconf2);
				star_one_sequent<configuration>(tr,machconf1',machconf2);
				
				star_trans_sequent<configuration>(tr,machconf1,machconf1',machconf2);

			}

			assert match_config(C, impconf2, machconf2) by {
				
				match_config_skip(C,k2,s2,pc2);

			}
			
		}
		
		case (CSeq(c1', c1''), k) => {
			assert {:split_here} true;
			var tr := (c1,c2) => transition(C,c1,c2);
			
			var (c1,k1,s1) := impconf1;
			var (c2,k2,s2) := impconf2;
			var (pc1,stk1,str1) := machconf1;

			
			
			bypass();
		}
		
		case (CIf(b, cifso, cifnotso), _) => {
			assert {:split_here} true;
			var tr := (c1,c2) => transition(C,c1,c2);
			
			var (c1,k1,s1) := impconf1;
			var (c2,k2,s2) := impconf2;
			var (pc1,stk1,str1) := machconf1;

			bypass();
		}
		
		case (CWhile(b, c), _) => {
			assert {:split_here} true;
			var tr := (c1,c2) => transition(C,c1,c2);
			
			var (c1,k1,s1) := impconf1;
			var (c2,k2,s2) := impconf2;
			var (pc1,stk1,str1) := machconf1;

			bypass();
		}
		
		case (CWhile(b, c), k) => {
			assert {:split_here} true;
			var tr := (c1,c2) => transition(C,c1,c2);
			
			var (c1,k1,s1) := impconf1;
			var (c2,k2,s2) := impconf2;
			var (pc1,stk1,str1) := machconf1;

			bypass();
		}
		
		case (CSkip, Kseq(c, k)) => {
			assert {:split_here} true;
			var tr := (c1,c2) => transition(C,c1,c2);
			
			var (c1,k1,s1) := impconf1;
			var (c2,k2,s2) := impconf2;
			var (pc1,stk1,str1) := machconf1;

			bypass();
		}
		
		case (CSkip, Kwhile(b, c, k)) =>	{
			assert {:split_here} true;
			var tr := (c1,c2) => transition(C,c1,c2);
			
			var (c1,k1,s1) := impconf1;
			var (c2,k2,s2) := impconf2;
			var (pc1,stk1,str1) := machconf1;

			bypass();
		}
		
	}
}
	
