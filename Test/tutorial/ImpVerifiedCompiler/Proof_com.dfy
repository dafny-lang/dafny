include "Imp.dfy"
include "ImpSem2.dfy"
include "MC.dfy"
include "Compiler.dfy"
include "Proof_aexp.dfy"
include "Proof_bexp.dfy"

least lemma compile_com_correct_terminating(s: store, c: com, s': store, C: code, pc: nat, stk: stack)		
	requires cexec(s,c,s')
	requires code_at(C,pc,compile_com(c))
	ensures transitions(C,(pc,stk,s),(pc + |compile_com(c)|, stk, s'))
{
	var tr := (c1,c2) => transition(C,c1,c2);
	match c {

		case CSkip => 

		case CAsgn(id, a) => {
			assert code_at(C,pc,compile_aexp(a)) by { resolve_code_at(); }
			var v := aeval(s,a);
			assert s' == s[id := v];
			var conf1 := (pc,stk,s);
			var conf2 := (pc + |compile_aexp(a)|, [aeval(s,a)] + stk, s);
			assert transitions(C,conf1,conf2) by {
				compile_aexp_correct(C,s,a,pc,stk);
			}
			var conf3 := (pc + |compile_aexp(a)| + 1, stk,s');
			assert transition(C,conf2,conf3);
			star_one_sequent<configuration>(tr,conf2,conf3);
			star_trans_sequent<configuration>(tr,conf1,conf2,conf3);
		}

		case CSeq(c1, c2) => {
			var C1 := compile_com(c1);
			var C2 := compile_com(c2);
			var conf1 := (pc,stk,s);
			var conf3 := (pc + |C1| + |C2|,stk,s');
			var si :| cexec(s,c1,si) && cexec(si,c2,s');
			var conf2 := (pc + |C1|,stk,si);
			assert code_at(C,pc,compile_com(c1)) by { resolve_code_at(); }
			compile_com_correct_terminating(s,c1,si,C,pc,stk);
			assert transitions(C,conf1,conf2);
			assert star<configuration>(tr,conf1,conf2);
			assert code_at(C,pc + |compile_com(c1)|,compile_com(c2)) by { resolve_code_at(); }
			compile_com_correct_terminating(si,c2,s',C,pc + |compile_com(c1)|,stk);
			assert transitions(C,conf2,conf3);
			assert star<configuration>(tr,conf2,conf3);
			star_trans_sequent<configuration>(tr,conf1,conf2,conf3);
		}

		case CIf(b, if_so, if_not) => {
			assert {:split_here} true;
			var bv := beval(s,b);
			var d1 := 0;
			var code_ifso := compile_com(if_so);
			var d0 := |code_ifso| + 1;
			var code_ifnot := compile_com(if_not);
			var code_prologue := compile_bexp(b,d1,d0);
			var conf1 := (pc,stk,s);
			
			if beval(s,b) {
				
				assert code_at(C,pc,compile_bexp(b,0,|code_ifso| + 1)) by { resolve_code_at(); }
				var conf2 := (pc + |compile_bexp(b,d1,d0)| + d1, stk, s);
				assert transitions(C,conf1,conf2) by { compile_bexp_correct_true(C,s,b,pc,d1,d0,stk); }
				assert star<configuration>(tr,conf1,conf2);

				assert cexec(s,if_so,s');
				assert code_at(C,pc + |compile_bexp(b,d1,d0)| + d1,compile_com(if_so)) by { resolve_code_at(); }

				var conf3 := (pc + |compile_bexp(b,d1,d0)| + d1 + |compile_com(if_so)|, stk, s');
				assert transitions(C,conf2,conf3) by {
					compile_com_correct_terminating(s,if_so,s',C,pc + |compile_bexp(b,d1,d0)| + d1,stk);
				}
				assert star<configuration>(tr,conf2,conf3);
				star_trans_sequent<configuration>(tr,conf1,conf2,conf3);
				
				// Not done yet, we should be facing a branch and need to jump!

				assert C[pc + |compile_bexp(b,d1,d0)| + d1 + |compile_com(if_so)|] == Ibranch(|compile_com(if_not)|);
				var conf4 := (pc + |compile_com(c)|, stk, s');
				assert transition(C,conf3,conf4);
				star_one_sequent<configuration>(tr,conf3,conf4);
				star_trans_sequent<configuration>(tr,conf1,conf3,conf4);
				
			} else {

				assert code_at(C,pc,compile_bexp(b,0,|code_ifso| + 1)) by { resolve_code_at(); }
				var conf2 := (pc + |compile_bexp(b,d1,d0)| + d0, stk, s);
				assert transitions(C,conf1,conf2) by { compile_bexp_correct_false(C,s,b,pc,d1,d0,stk); }
				assert star<configuration>(tr,conf1,conf2);

				assert cexec(s,if_not,s');
				assert code_at(C,pc + |compile_bexp(b,d1,d0)| + d0,compile_com(if_not)) by { resolve_code_at(); }

				var conf3 := (pc + |compile_bexp(b,d1,d0)| + d0 + |compile_com(if_not)|, stk, s');
				assert transitions(C,conf2,conf3) by {
					compile_com_correct_terminating(s,if_not,s',C,pc + |compile_bexp(b,d1,d0)| + d0,stk);
				}
				assert star<configuration>(tr,conf2,conf3);
				star_trans_sequent<configuration>(tr,conf1,conf2,conf3);
				
			}

		}

		case CWhile(b, body) => {
			assert {:split_here} true;

			var conf1 := (pc,stk,s);
			var d1 := 0;
			var d0 := |compile_com(body)| + 1;

			if beval(s,b) {

				// Simulation of the test
				assert code_at(C,pc,compile_bexp(b,d1,d0)) by { resolve_code_at(); }
				var conf2 := (pc + |compile_bexp(b,d1,d0)| + d1, stk, s);
				assert transitions(C,conf1,conf2) by { compile_bexp_correct_true(C,s,b,pc,d1,d0,stk); }
				assert star<configuration>(tr,conf1,conf2);

				var si :| cexec(s,body,si) && cexec(si,CWhile(b,body),s');

				// Simulation of the loop body
				var conf3 := (pc + |compile_bexp(b,d1,d0)| + d1 + |compile_com(body)|,stk,si);
				assert code_at(C,pc + |compile_bexp(b,d1,d0)| + d1,compile_com(body)) by { resolve_code_at(); }
				assert transitions(C,conf2,conf3) by {
					compile_com_correct_terminating(s,body,si,C,pc + |compile_bexp(b,d1,d0)| + d1,stk);
				}
				assert star<configuration>(tr,conf2,conf3);
				star_trans_sequent<configuration>(tr,conf1,conf2,conf3);

				// Branch back
				assert C[pc + |compile_bexp(b,d1,d0)| + d1 + |compile_com(body)|]
				== Ibranch(-( |compile_bexp(b,d1,d0)| + |compile_com(body)| + 1));
				var conf4 := (pc,stk,si);
				assert transition(C,conf3,conf4);
				star_one_sequent<configuration>(tr,conf3,conf4);
				star_trans_sequent<configuration>(tr,conf1,conf3,conf4);
				
				// And now we have done our due diligence, we simulated one iteration of the loop, and
				// recursively simulate the rest

				var conf5 := (pc + |compile_bexp(b,d1,d0)| + |compile_com(body)| + 1,stk,s');
				assert code_at(C,pc,compile_com(CWhile(b,body))) by { resolve_code_at(); }
				assert transitions(C,conf4,conf5) by {
					compile_com_correct_terminating(si,CWhile(b,body),s',C,pc,stk);
				}
				assert star<configuration>(tr,conf4,conf5);
				star_trans_sequent<configuration>(tr,conf1,conf4,conf5);
				
			} else {

				assert code_at(C,pc,compile_bexp(b,d1,d0)) by { resolve_code_at(); }
				var conf2 := (pc + |compile_bexp(b,d1,d0)| + d0, stk, s);
				assert transitions(C,conf1,conf2) by { compile_bexp_correct_false(C,s,b,pc,d1,d0,stk); }
				assert star<configuration>(tr,conf1,conf2);
				
			}
			
		}
	}
}
