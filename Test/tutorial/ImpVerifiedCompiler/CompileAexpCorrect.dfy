include "Imp.dfy"
include "ImpNaturalSem.dfy"
include "Mach.dfy"
include "MachSemantics.dfy"
include "Compiler.dfy"
include "SimulationRelation.dfy"

lemma compile_aexp_correct(C: code, s: store, a: aexp, pc: nat, stk: stack)
	requires forall id: ident :: id_in_aexp(id,a) ==> id in s
	requires code_at(C,pc,compile_aexp(a))
	ensures transitions(C,(pc,stk,s),(pc + |compile_aexp(a)|, [aeval(s,a)] + stk, s))
{
	var conf1 := (pc,stk,s);
	var conf2 := (pc + |compile_aexp(a)|, [aeval(s,a)] + stk, s);
	var tr := (c1,c2) => transition(C,c1,c2);
	match a {

		case AConst(n) => { 

			assert aeval(s,a) == n;
			assert compile_aexp(a) == [Iconst(n)];
			assert |compile_aexp(a)| == 1;
			assert C[pc] == Iconst(n);
			assert transition(C,(pc,stk,s),(pc + 1, [n] + stk,s));
			assert transition(C,(pc,stk,s),(pc + |compile_aexp(a)|, [aeval(s,a)] + stk,s));
			star_one_sequent<configuration>(tr,(pc,stk,s),(pc + |compile_aexp(a)|, [aeval(s,a)] + stk,s));
			
		}
		
		case AId(id) => star_one_sequent<configuration>(tr,conf1,conf2);

		case APlus(a1, a2) => {
			assert code_at(C,pc,compile_aexp(a1)) by { resolve_code_at(); }
			compile_aexp_correct(C,s,a1,pc,stk);
			assert code_at(C,pc + |compile_aexp(a1)|,compile_aexp(a2)) by { resolve_code_at(); }
			compile_aexp_correct(C,s,a2,pc + |compile_aexp(a1)|,[aeval(s,a1)] + stk);
			var confi1 := (pc + |compile_aexp(a1)|,[aeval(s,a1)] + stk,s);
			assert star<configuration>(tr,conf1,confi1);  
			var confi2 := (pc + |compile_aexp(a1)| + |compile_aexp(a2)|,[aeval(s,a2)] + ([aeval(s,a1)] + stk),s);
			assert star<configuration>(tr,confi1,confi2);
			star_trans_sequent<configuration>(tr,conf1,confi1,confi2);
			star_one_sequent<configuration>(tr,confi2,conf2);
			star_trans_sequent<configuration>(tr,conf1,confi2,conf2);
		}

		case AMinus(a1, a2) => {
			assert code_at(C,pc,compile_aexp(a1)) by { resolve_code_at(); }
			compile_aexp_correct(C,s,a1,pc,stk);
			assert code_at(C,pc + |compile_aexp(a1)|,compile_aexp(a2)) by { resolve_code_at(); }
			compile_aexp_correct(C,s,a2,pc + |compile_aexp(a1)|,[aeval(s,a1)] + stk);
			var confi1 := (pc + |compile_aexp(a1)|,[aeval(s,a1)] + stk,s);
			assert star<configuration>(tr,conf1,confi1);  
			var confi2 := (pc + |compile_aexp(a1)| + |compile_aexp(a2)|,[aeval(s,a2)] + ([aeval(s,a1)] + stk),s);
			assert star<configuration>(tr,confi1,confi2);
			star_trans_sequent<configuration>(tr,conf1,confi1,confi2);
			var confi3 := (pc + |compile_aexp(a1)| + |compile_aexp(a2)| + 1,[-aeval(s,a2)] + ([aeval(s,a1)] + stk),s);
			star_one_sequent<configuration>(tr,confi2,confi3);
			star_one_sequent<configuration>(tr,confi3,conf2);
			star_trans_sequent<configuration>(tr,conf1,confi2,conf2);
			
		}
	}
}

lemma compile_aexp_correct_gen()
	ensures forall C: code :: forall s: store :: forall a: aexp :: forall pc: nat :: forall stk: stack :: (forall id: ident :: id_in_aexp(id,a) ==> id in s) ==> code_at(C,pc,compile_aexp(a)) ==> transitions(C,(pc,stk,s),(pc + |compile_aexp(a)|, [aeval(s,a)] + stk, s)) {
		forall C, s, a, pc: nat, stk ensures (forall id: ident :: id_in_aexp(id,a) ==> id in s) ==> code_at(C,pc,compile_aexp(a)) ==> transitions(C,(pc,stk,s),(pc + |compile_aexp(a)|, [aeval(s,a)] + stk, s)) {
			if (forall id: ident :: id_in_aexp(id,a) ==> id in s) {
				if code_at(C,pc,compile_aexp(a)) {
					compile_aexp_correct(C, s, a, pc, stk);
				}
			}
		}
}
