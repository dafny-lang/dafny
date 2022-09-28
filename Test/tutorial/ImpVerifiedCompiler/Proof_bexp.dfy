include "Imp.dfy"
include "ImpSem2.dfy"
include "MC.dfy"
include "Compiler.dfy"
include "Proof_aexp.dfy"

lemma compile_bexp_correct_true(C: code, s: store, b: bexp, pc: nat, d1: nat, d0: nat, stk: stack)
	requires forall id: ident :: id_in_bexp(id,b) ==> id in s
	requires code_at(C,pc,compile_bexp(b,d1,d0))
	requires beval(s,b)
	ensures transitions(C,(pc,stk,s),(pc + |compile_bexp(b,d1,d0)| + d1, stk, s))
{
	var tr := (c1,c2) => transition(C,c1,c2);
	
	match b {

		case BTrue => {
			assert {:split_here} true;
			if d1 == 0 {
			} else {
				var conf1 := (pc,stk,s);
				var conf2 := (pc + |compile_bexp(b,d1,d0)| + d1, stk, s);
				assert beval(s,b); 
				assert C[pc] == Ibranch(d1);
				assert transition(C,conf1,conf2);
				star_one_sequent<configuration>(tr,conf1,conf2);
			}
		}
		
		case BFalse => assert !beval(s,b);
			
		case BEq(a1, a2) => {
			assert {:split_here} true;			

			var conf1 := (pc,stk,s);
			var conf2 := (pc + |compile_aexp(a1)|, [aeval(s,a1)] + stk, s);
			assert transitions(C,conf1,conf2) by { resolve_code_at(); compile_aexp_correct_gen(); }
			assert star<configuration>(tr,conf1,conf2);
			
			var conf3i := ((pc + |compile_aexp(a1)|) + |compile_aexp(a2)|, [aeval(s,a2)] + ([aeval(s,a1)] + stk), s);
			assert transitions(C,conf2,conf3i) by { resolve_code_at(); compile_aexp_correct_gen(); }

			var conf3 := (pc + |compile_aexp(a1)| + |compile_aexp(a2)|, [aeval(s,a2)] + [aeval(s,a1)] + stk, s);
			assert transitions(C,conf2,conf3) by {
				assert (pc + |compile_aexp(a1)|) + |compile_aexp(a2)| == pc + |compile_aexp(a1)| + |compile_aexp(a2)|;
				assert [aeval(s,a2)] + ([aeval(s,a1)] + stk) == [aeval(s,a2)] + [aeval(s,a1)] + stk;
			}
			assert star<configuration>(tr,conf2,conf3);
			
			var stk' := [aeval(s,a2)] + [aeval(s,a1)] + stk;
			assert C[pc + |compile_aexp(a1)| + |compile_aexp(a2)|] == Ibeq(d1,d0);
			assert stk == stk'[2..];
			assert |stk'| > 1;
			var pcs := pc + |compile_aexp(a1)| + |compile_aexp(a2)|;
			assert pc + |compile_bexp(b,d1,d0)| + d1 == pcs + 1 + (if stk'[0] == stk'[1] then d1 else d0);

			var conf4 := (pc + |compile_bexp(b,d1,d0)| + d1, stk, s);
			assert transition(C,conf3,conf4);
			
			star_one_sequent<configuration>(tr,conf3,conf4);

			star_trans_sequent<configuration>(tr,conf1,conf2,conf3);
			star_trans_sequent<configuration>(tr,conf1,conf3,conf4);
			
			}

		case BLe(a1, a2) => {
			assert {:split_here} true;

			var conf1 := (pc,stk,s);
			var conf2 := (pc + |compile_aexp(a1)|, [aeval(s,a1)] + stk, s);
			assert transitions(C,conf1,conf2) by { resolve_code_at(); compile_aexp_correct_gen(); }
			assert star<configuration>(tr,conf1,conf2);
			
			var conf3i := ((pc + |compile_aexp(a1)|) + |compile_aexp(a2)|, [aeval(s,a2)] + ([aeval(s,a1)] + stk), s);
			assert transitions(C,conf2,conf3i) by { resolve_code_at(); compile_aexp_correct_gen(); }

			var conf3 := (pc + |compile_aexp(a1)| + |compile_aexp(a2)|, [aeval(s,a2)] + [aeval(s,a1)] + stk, s);
			assert transitions(C,conf2,conf3) by {
				assert (pc + |compile_aexp(a1)|) + |compile_aexp(a2)| == pc + |compile_aexp(a1)| + |compile_aexp(a2)|;
				assert [aeval(s,a2)] + ([aeval(s,a1)] + stk) == [aeval(s,a2)] + [aeval(s,a1)] + stk;
			}
			assert star<configuration>(tr,conf2,conf3);
			
			var stk' := [aeval(s,a2)] + [aeval(s,a1)] + stk;
			assert C[pc + |compile_aexp(a1)| + |compile_aexp(a2)|] == Ible(d1,d0);
			assert stk == stk'[2..];
			assert |stk'| > 1;
			var pcs := pc + |compile_aexp(a1)| + |compile_aexp(a2)|;
			assert pc + |compile_bexp(b,d1,d0)| + d1 == pcs + 1 + (if stk'[1] <= stk'[0] then d1 else d0);

			var conf4 := (pc + |compile_bexp(b,d1,d0)| + d1, stk, s);
			assert transition(C,conf3,conf4);
			
			star_one_sequent<configuration>(tr,conf3,conf4);

			star_trans_sequent<configuration>(tr,conf1,conf2,conf3);
			star_trans_sequent<configuration>(tr,conf1,conf3,conf4);			
			
			}
			
		case BNot(b1) => {
			assert {:split_here} true;
			
			var conf1 := (pc,stk,s);
			assert !beval(s,b1);

			compile_bexp_correct_false(C, s, b1, pc, d0, d1, stk);
			
			}
			
		case BAnd(b1, b2) => {
			assert {:split_here} true;

			var conf1 := (pc,stk,s);
			assert code_at(C,pc,compile_bexp(b1, 0, |compile_bexp(b2, d1, d0)| + d0)) by { resolve_code_at(); }
			var conf2 := (pc + |compile_bexp(b1, 0, |compile_bexp(b2, d1, d0)| + d0)|,stk,s);
			assert transitions(C,conf1,conf2) by {
				compile_bexp_correct_true(C, s, b1, pc, 0, |compile_bexp(b2, d1, d0)| + d0, stk);
			}
			assert star<configuration>(tr,conf1,conf2);

			assert code_at(C,pc + |compile_bexp(b1, 0, |compile_bexp(b2, d1, d0)| + d0)|,compile_bexp(b2, d1, d0)) by { resolve_code_at(); }
			var conf3 := (pc + |compile_bexp(b1, 0, |compile_bexp(b2, d1, d0)| + d0)| + |compile_bexp(b2, d1, d0)| + d1,stk,s);
			assert transitions(C,conf2,conf3) by {
			 	compile_bexp_correct_true(C, s, b2, pc + |compile_bexp(b1, 0, |compile_bexp(b2, d1, d0)| + d0)|, d1, d0, stk);
			}
			assert star<configuration>(tr,conf2,conf3);
			star_trans_sequent<configuration>(tr,conf1,conf2,conf3);
			
			}
		
	}
	
}

lemma compile_bexp_correct_false(C: code, s: store, b: bexp, pc: nat, d1: nat, d0: nat, stk: stack)
	requires forall id: ident :: id_in_bexp(id,b) ==> id in s
	requires code_at(C,pc,compile_bexp(b,d1,d0))
	requires !beval(s,b)
	ensures transitions(C,(pc,stk,s),(pc + (|compile_bexp(b,d1,d0)| + d0), stk, s))
{
	var tr := (c1,c2) => transition(C,c1,c2);
	
	match b {

		case BTrue => assert beval(s,b);
		
		case BFalse => {
			assert {:split_here} true;
			if d0 == 0 {
			} else {
				var conf1 := (pc,stk,s);
				var conf2 := (pc + |compile_bexp(b,d1,d0)| + d0, stk, s);
				assert !beval(s,b); 
				assert C[pc] == Ibranch(d0);
				assert transition(C,conf1,conf2);
				star_one_sequent<configuration>(tr,conf1,conf2);
			}
		}
			
		case BEq(a1, a2) => {
			assert {:split_here} true;			

			var conf1 := (pc,stk,s);
			var conf2 := (pc + |compile_aexp(a1)|, [aeval(s,a1)] + stk, s);
			assert transitions(C,conf1,conf2) by { resolve_code_at(); compile_aexp_correct_gen(); }
			assert star<configuration>(tr,conf1,conf2);
			
			var conf3i := ((pc + |compile_aexp(a1)|) + |compile_aexp(a2)|, [aeval(s,a2)] + ([aeval(s,a1)] + stk), s);
			assert transitions(C,conf2,conf3i) by { resolve_code_at(); compile_aexp_correct_gen(); }

			var conf3 := (pc + |compile_aexp(a1)| + |compile_aexp(a2)|, [aeval(s,a2)] + [aeval(s,a1)] + stk, s);
			assert transitions(C,conf2,conf3) by {
				assert (pc + |compile_aexp(a1)|) + |compile_aexp(a2)| == pc + |compile_aexp(a1)| + |compile_aexp(a2)|;
				assert [aeval(s,a2)] + ([aeval(s,a1)] + stk) == [aeval(s,a2)] + [aeval(s,a1)] + stk;
			}
			assert star<configuration>(tr,conf2,conf3);
			
			var stk' := [aeval(s,a2)] + [aeval(s,a1)] + stk;
			assert C[pc + |compile_aexp(a1)| + |compile_aexp(a2)|] == Ibeq(d1,d0);
			assert stk == stk'[2..];
			assert |stk'| > 1;
			var pcs := pc + |compile_aexp(a1)| + |compile_aexp(a2)|;
			assert pc + |compile_bexp(b,d1,d0)| + d0 == pcs + 1 + (if stk'[0] == stk'[1] then d1 else d0);

			var conf4 := (pc + |compile_bexp(b,d1,d0)| + d0, stk, s);
			assert transition(C,conf3,conf4);
			
			star_one_sequent<configuration>(tr,conf3,conf4);

			star_trans_sequent<configuration>(tr,conf1,conf2,conf3);
			star_trans_sequent<configuration>(tr,conf1,conf3,conf4);
			
			}

		case BLe(a1, a2) => {
			assert {:split_here} true;

			var conf1 := (pc,stk,s);
			var conf2 := (pc + |compile_aexp(a1)|, [aeval(s,a1)] + stk, s);
			assert transitions(C,conf1,conf2) by { resolve_code_at(); compile_aexp_correct_gen(); }
			assert star<configuration>(tr,conf1,conf2);
			
			var conf3i := ((pc + |compile_aexp(a1)|) + |compile_aexp(a2)|, [aeval(s,a2)] + ([aeval(s,a1)] + stk), s);
			assert transitions(C,conf2,conf3i) by { resolve_code_at(); compile_aexp_correct_gen(); }

			var conf3 := (pc + |compile_aexp(a1)| + |compile_aexp(a2)|, [aeval(s,a2)] + [aeval(s,a1)] + stk, s);
			assert transitions(C,conf2,conf3) by {
				assert (pc + |compile_aexp(a1)|) + |compile_aexp(a2)| == pc + |compile_aexp(a1)| + |compile_aexp(a2)|;
				assert [aeval(s,a2)] + ([aeval(s,a1)] + stk) == [aeval(s,a2)] + [aeval(s,a1)] + stk;
			}
			assert star<configuration>(tr,conf2,conf3);
			
			var stk' := [aeval(s,a2)] + [aeval(s,a1)] + stk;
			assert C[pc + |compile_aexp(a1)| + |compile_aexp(a2)|] == Ible(d1,d0);
			assert stk == stk'[2..];
			assert |stk'| > 1;
			var pcs := pc + |compile_aexp(a1)| + |compile_aexp(a2)|;
			assert pc + |compile_bexp(b,d1,d0)| + d0 == pcs + 1 + (if stk'[1] <= stk'[0] then d1 else d0);

			var conf4 := (pc + |compile_bexp(b,d1,d0)| + d0, stk, s);
			assert transition(C,conf3,conf4);
			
			star_one_sequent<configuration>(tr,conf3,conf4);

			star_trans_sequent<configuration>(tr,conf1,conf2,conf3);
			star_trans_sequent<configuration>(tr,conf1,conf3,conf4);			
			
			}
			
		case BNot(b1) => {
			assert {:split_here} true;
			
			var conf1 := (pc,stk,s);
			assert beval(s,b1);

			compile_bexp_correct_true(C, s, b1, pc, d0, d1, stk);
			
			}
			
		case BAnd(b1, b2) => {
			assert {:split_here} true;

			// This case if more interesting because and is compiled as a lazy and.
			// So, if it is false, two things could have happened
			// If eval(s,b1) was false, we branched directly without executing b2
			// Otherwise, eval(s,b2) was false

			if beval(s,b1) {

				assert !beval(s,b2);

				var conf1 := (pc,stk,s);

				assert code_at(C,pc,compile_bexp(b1, 0, |compile_bexp(b2, d1, d0)| + d0)) by { resolve_code_at(); }
				var conf2 := (pc + |compile_bexp(b1, 0, |compile_bexp(b2, d1, d0)| + d0)|,stk,s);
				assert transitions(C,conf1,conf2) by {
					compile_bexp_correct_true(C, s, b1, pc, 0, |compile_bexp(b2, d1, d0)| + d0, stk);
				}
				assert star<configuration>(tr,conf1,conf2);

				assert code_at(C,pc + |compile_bexp(b1, 0, |compile_bexp(b2, d1, d0)| + d0)|,compile_bexp(b2, d1, d0)) by { resolve_code_at(); }
				var conf3 := (pc + |compile_bexp(b1, 0, |compile_bexp(b2, d1, d0)| + d0)| + |compile_bexp(b2, d1, d0)| + d0,stk,s);
				assert transitions(C,conf2,conf3) by {
			 		compile_bexp_correct_false(C, s, b2, pc + |compile_bexp(b1, 0, |compile_bexp(b2, d1, d0)| + d0)|, d1, d0, stk);
				}
				assert star<configuration>(tr,conf2,conf3);
				star_trans_sequent<configuration>(tr,conf1,conf2,conf3);

			} else {

				var conf1 := (pc,stk,s);

				assert code_at(C,pc,compile_bexp(b1, 0, |compile_bexp(b2, d1, d0)| + d0)) by { resolve_code_at(); }	
				var conf2 := (pc + |compile_bexp(b1, 0, |compile_bexp(b2, d1, d0)| + d0)| + |compile_bexp(b2, d1, d0)| + d0,stk,s);
				assert transitions(C,conf1,conf2) by {
					compile_bexp_correct_false(C, s, b1, pc, 0, |compile_bexp(b2, d1, d0)| + d0, stk);
				}
				assert star<configuration>(tr,conf1,conf2);
				
			}
			
		}
			
	}
	
}
