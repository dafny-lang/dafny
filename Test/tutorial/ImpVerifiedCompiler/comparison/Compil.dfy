include "Sequences.dfy"
include "IMP.dfy"

type offset = int

datatype instruction =
  | Iconst(n: int)
  | Ivar(x: ident)
  | Isetvar(x: string)
  | Iadd
	| Iopp
  | Ibranch(d: offset)
  | Ibeq(d1: offset, d0: offset)
  | Ible(d1: offset, d0: offset)
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

predicate machine_diverges(C: code, s_init: store) {
	infseq((c1,c2) => transition(C,c1,c2),(0,[],s_init))
}

function method compile_aexp(a: aexp): code {
	match a {
		case CONST(n) => [Iconst(n)]
		case VAR(id) => [Ivar(id)]
		case PLUS(a1, a2) => compile_aexp(a1) + compile_aexp(a2) + [Iadd]
		case MINUS(a1, a2) => compile_aexp(a1) + compile_aexp(a2) + [Iopp,Iadd]
	}
}

function method negb(b: bool): bool {
	if b then false else true
}

function method compile_bexp(b: bexp, d1: int, d0: int): code {
  match b {
		case TRUE => if d1 == 0 then [] else [Ibranch(d1)]
		case FALSE => if d0 == 0 then [] else [Ibranch(d0)]
		case EQUAL(a1, a2) => compile_aexp(a1) + compile_aexp(a2) + [Ibeq(d1,d0)]   
		case LESSEQUAL(a1, a2) => compile_aexp(a1) + compile_aexp(a2) + [Ible(d1,d0)]
		case NOT(b1) => compile_bexp(b1, d0, d1)
		case AND(b1, b2) =>
      var c2 := compile_bexp(b2, d1, d0);
      var c1 := compile_bexp(b1, 0, |c2| + d0);
      c1 + c2
	}
}

function method compile_com(c: com): code {
	match c {
		case SKIP => []
		case ASSIGN(id, a) => compile_aexp(a) + [Isetvar(id)]
		case SEQ(c1, c2) => compile_com(c1) + compile_com(c2)
		case IFTHENELSE(b, ifso, ifnot) =>
			var code_ifso := compile_com(ifso);
			var code_ifnot := compile_com(ifnot);
			compile_bexp(b,0,|code_ifso| + 1)
			+ code_ifso + [Ibranch(|code_ifnot|)] + code_ifnot
		case WHILE(b, body) =>
			var code_body := compile_com(body);
			var code_test := compile_bexp(b,0,|code_body|+1);
			code_test + code_body + [Ibranch(-( |code_test| + |code_body| + 1))]
	}
}

function method compile_program(p: com): code {
	compile_com(p) + [Ihalt]
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

lemma compile_aexp_correct(C: code, s: store, a: aexp, pc: nat, stk: stack)
	requires forall id: ident :: id_in_aexp(id,a) ==> id in s
	requires code_at(C,pc,compile_aexp(a))
	ensures transitions(C,(pc,stk,s),(pc + |compile_aexp(a)|, [aeval(s,a)] + stk, s))
{
	var conf1 := (pc,stk,s);
	var conf2 := (pc + |compile_aexp(a)|, [aeval(s,a)] + stk, s);
	var tr := (c1,c2) => transition(C,c1,c2);
	match a {

		case CONST(n) => { 

			assert aeval(s,a) == n;
			assert compile_aexp(a) == [Iconst(n)];
			assert |compile_aexp(a)| == 1;
			assert C[pc] == Iconst(n);
			assert transition(C,(pc,stk,s),(pc + 1, [n] + stk,s));
			assert transition(C,(pc,stk,s),(pc + |compile_aexp(a)|, [aeval(s,a)] + stk,s));
			star_one_sequent<configuration>(tr,(pc,stk,s),(pc + |compile_aexp(a)|, [aeval(s,a)] + stk,s));
			
		}
		
		case VAR(id) => star_one_sequent<configuration>(tr,conf1,conf2);

		case PLUS(a1, a2) => {
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

		case MINUS(a1, a2) => {
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

lemma compile_bexp_correct_true(C: code, s: store, b: bexp, pc: nat, d1: nat, d0: nat, stk: stack)
	requires forall id: ident :: id_in_bexp(id,b) ==> id in s
	requires code_at(C,pc,compile_bexp(b,d1,d0))
	requires beval(s,b)
	ensures transitions(C,(pc,stk,s),(pc + |compile_bexp(b,d1,d0)| + d1, stk, s))
{
	var tr := (c1,c2) => transition(C,c1,c2);
	
	match b {

		case TRUE => {
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
		
		case FALSE => assert !beval(s,b);
			
		case EQUAL(a1, a2) => {
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

		case LESSEQUAL(a1, a2) => {
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
			
		case NOT(b1) => {
			assert {:split_here} true;
			
			var conf1 := (pc,stk,s);
			assert !beval(s,b1);

			compile_bexp_correct_false(C, s, b1, pc, d0, d1, stk);
			
			}
			
		case AND(b1, b2) => {
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

		case TRUE => assert beval(s,b);
		
		case FALSE => {
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
			
		case EQUAL(a1, a2) => {
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

		case LESSEQUAL(a1, a2) => {
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
			
		case NOT(b1) => {
			assert {:split_here} true;
			
			var conf1 := (pc,stk,s);
			assert beval(s,b1);

			compile_bexp_correct_true(C, s, b1, pc, d0, d1, stk);
			
			}
			
		case AND(b1, b2) => {
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

least lemma compile_com_correct_terminating(s: store, c: com, s': store, C: code, pc: nat, stk: stack)		
	requires cexec(s,c,s')
	requires code_at(C,pc,compile_com(c))
	ensures transitions(C,(pc,stk,s),(pc + |compile_com(c)|, stk, s'))
{
	var tr := (c1,c2) => transition(C,c1,c2);
	match c {

		case SKIP => 

		case ASSIGN(id, a) => {
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

		case SEQ(c1, c2) => {
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

		case IFTHENELSE(b, if_so, if_not) => {
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

		case WHILE(b, body) => {
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

				var si :| cexec(s,body,si) && cexec(si,WHILE(b,body),s');

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
				assert code_at(C,pc,compile_com(WHILE(b,body))) by { resolve_code_at(); }
				assert transitions(C,conf4,conf5) by {
					compile_com_correct_terminating(si,WHILE(b,body),s',C,pc,stk);
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

lemma compile_program_correct_terminating(s: store, c: com, s': store)
	requires cexec(s,c,s')
	ensures machine_terminates(compile_program(c),s,s')
{
	var C := compile_program(c);
	var pc := |C|-1;
	assert pc < |C|;
	assert code_at(C,0,compile_com(c)) by {
		assert C == [] + compile_com(c) + [Ihalt];
	}
	compile_com_correct_terminating(s,c,s',C,0,[]);
	assert transitions(C,(0,[],s),(pc,[],s'));
	assert compile_program(c)[pc] == Ihalt;
	
}

least predicate compile_cont(C: code, k: cont, pc: nat) {
	if ! (pc < |C|) then false else
	 (match (k,C[pc]) {
		case (Kstop,Ihalt) => true
		case _ => false
	 })
	 ||
		((match (k,C[pc]) {
	 		case (Kseq(c,k),_) =>
	 			var pc': nat := pc + |compile_com(c)|;
	 			&& code_at(C, pc, (compile_com(c)))
	 				&& compile_cont(C, k, pc')
	 		case _ => false
		})
		||
			((match (k,C[pc]) {
				case (Kwhile(b,c,k),Ibranch(ofs)) =>
					var pc' := pc + 1 + ofs;
					var pc'' := pc' + |compile_com(WHILE(b, c))|;
					&& (pc' >= 0)
						&& (pc'' >= 0)	
						&& code_at(C, pc', (compile_com(WHILE(b, c)))) 
						&& compile_cont(C, k, pc'')
				case _ => false
			})
			||
				(match (k,C[pc]) {
					case (_,Ibranch(ofs)) =>
						var pc' := pc + 1 + ofs;
						&& pc' >= 0
							&& compile_cont(C, k, pc')
					case _ => false
				})))
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
	ensures match_config(C, (SKIP, k, s), (pc, [], s))
{

	assert pc < |C|;
	var Cleft := C[..pc];
	assert |Cleft| == pc;
	var Cright := C[pc..];
	assert C == Cleft + Cright;
	var Cmid := [];
	assert C == Cleft + Cmid + Cright;

}

least lemma compile_cont_Kstop_inv(C: code, pc: nat, s: store)
	requires compile_cont(C,Kstop,pc)
	ensures exists pc': nat :: star((c1,c2) => transition(C,c1,c2), (pc, [], s), (pc', [], s)) && pc' < |C| && C[pc'] == Ihalt
{

	match C[pc] {
		case Ihalt =>
		case Ibranch(ofs) => {
			var pc' := pc + 1 + ofs;
			assert pc' >= 0;
			assert compile_cont(C,Kstop,pc');
			compile_cont_Kstop_inv(C,pc',s);
		}
		case _ => 
	}
		
}

least lemma compile_cont_Kseq_inv(C: code, c: com, k: cont, pc: nat, s: store)
	requires compile_cont(C,Kseq(c,k),pc)
	ensures exists pc': nat :: star((c1,c2) => transition(C,c1,c2),(pc, [], s),(pc', [], s)) && code_at(C,pc',compile_com(c)) && compile_cont(C,k,pc' + |compile_com(c)|)
{
}

lemma compile_cont_Kwhile_simp(C: code, b: bexp, c: com, k: cont, pc: nat, s: store, ofs: int)
	requires compile_cont(C,Kwhile(b,c,k),pc)
	requires C[pc] == Ibranch(ofs)
	ensures 
	|| (pc + 1 + ofs >= 0 && compile_cont(C, Kwhile(b,c,k), pc + 1 + ofs))
	|| (&& pc + 1 + ofs >= 0
	   && (pc + 1 + ofs) + |compile_com(WHILE(b, c))| >= 0
 		 && code_at(C, pc + 1 + ofs, (compile_com(WHILE(b, c))))
 		 && compile_cont(C, k, (pc + 1 + ofs) + |compile_com(WHILE(b, c))|))
{
}
		 

least lemma compile_cont_Kwhile_inv(C: code, b: bexp, c: com, k: cont, pc: nat, s: store)
	requires compile_cont(C,Kwhile(b,c,k),pc)
	ensures exists pc': nat :: plus((c1,c2) => transition(C,c1,c2),(pc, [], s),(pc', [], s)) && code_at(C,pc',compile_com(WHILE(b,c))) && compile_cont(C,k,pc' + |compile_com(WHILE(b,c))|)
{

	match C[pc] {

		case Ibranch(ofs) => {

			compile_cont_Kwhile_simp(C,b,c,k,pc,s,ofs);

			if pc + 1 + ofs > 0 && compile_cont(C, Kwhile(b,c,k), pc + 1 + ofs) {

 				var pc': nat := pc + 1 + ofs;

				assert transition(C,(pc, [], s),(pc', [], s));
 				plus_one<configuration>((c1,c2) => transition(C,c1,c2),(pc, [], s),(pc', [], s));
				
				compile_cont_Kwhile_inv(C,b,c,k,pc',s);
				
 			} else {

				assert transition(C,(pc, [], s),(pc + 1 + ofs, [], s));
 				plus_one<configuration>((c1,c2) => transition(C,c1,c2),(pc, [], s),(pc + 1 + ofs, [], s));
				
			}
			
		}
		
		case _ =>

	}

}

function com_size(c: com): nat {

	match c {
		case SKIP => 1
		case ASSIGN(_,_) => 1 
		case SEQ(c1,c2) => com_size(c1) + com_size(c2) + 1
		case IFTHENELSE(b,c1,c2) => com_size(c1) + com_size(c2) + 1 
		case WHILE(b,c) => com_size(c) + 1 
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

lemma nat_is_pos(n: nat)
	ensures n >= 0
{
}

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
		
		case (ASSIGN(i, a), _) => {
			assert {:split_here} true;
			var tr := (c1,c2) => transition(C,c1,c2);
			
			var (c1,k1,s1) := impconf1;
			var (c2,k2,s2) := impconf2;
			var (pc1,stk1,str1) := machconf1;

			assert (c2,k2,s2) == (SKIP,k1,s1[i := aeval(s1,a)]);

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
		
		case (SEQ(c1', c1''), k) => {
			assert {:split_here} true;
			var tr := (c1,c2) => transition(C,c1,c2);
			
			var (c1,k1,s1) := impconf1;
			var (c2,k2,s2) := impconf2;
			var (pc1,stk1,str1) := machconf1;

			assert (c2,k2,s2) == (c1',Kseq(c1'',k),s2);
			
			assert (pc1,stk1,str1) == (pc1,[],s1);

			var machconf2: configuration := machconf1; 
			var (pc2,stk2,str2) := machconf2;

			assert measure(impconf2) < measure(impconf1);
			
			assert star(tr,machconf1,machconf2);

			assert match_config(C, impconf2, machconf2) by {

				assert s2 == str2;
				assert stk2 == [];
				assert code_at(C, pc2, compile_com(c2)) by {
					assert pc2 == pc1;
					assert compile_com(c2) == compile_com(c1');
					assert code_at(C,pc1,compile_com(c1')) by { resolve_code_at(); }
				}
				assert compile_cont(C, k2, pc2 + |compile_com(c2)|) by {
					assert k2 == Kseq(c1'',k1);
					assert pc2 == pc1;
					assert compile_com(c2) == compile_com(c1');
					assert code_at(C, pc1 + |compile_com(c1')|, compile_com(c1'')) by { resolve_code_at(); }
					assert compile_cont(C,k1,pc1 + |compile_com(c1')| + |compile_com(c1'')|);
					assert compile_cont(C, Kseq(c1'',k1), pc1 + |compile_com(c1')|);
				}	
			}
		}
		
		case (IFTHENELSE(b, cifso, cifnotso), _) => {
			assert {:split_here} true;
			var tr := (c1,c2) => transition(C,c1,c2);
			
			var (c1,k1,s1) := impconf1;
			var (c2,k2,s2) := impconf2;
			var (pc1,stk1,str1) := machconf1;

			var d1 := 0;
			var code_ifso := compile_com(cifso);
			var d0 := |code_ifso| + 1;
			var code_ifnot := compile_com(cifnotso);
			var code_prologue := compile_bexp(b,d1,d0);
			
			if beval(s1,b) {

				assert (c2,k2,s2) == (cifso,k1,s1);

				assert code_at(C,pc1,compile_bexp(b,0,|code_ifso| + 1)) by { resolve_code_at(); }
				var machconf2 := (pc1 + |compile_bexp(b,d1,d0)| + d1, stk1, s1);
				assert transitions(C,machconf1,machconf2) by { compile_bexp_correct_true(C,str1,b,pc1,d1,d0,stk1); }
				assert star<configuration>(tr,machconf1,machconf2);

				// Interesting example: if you hoist these two asserts, then the match_config cannot be concluded
				assert match_config(C, impconf2, machconf2) by {

					assert code_at(C, machconf2.0, compile_com(impconf2.0)) by { resolve_code_at(); }
					assert compile_cont(C, impconf2.1, (machconf2.0 + |compile_com(impconf2.0)|) + 1 + |compile_com(cifnotso)|);
					assert C[machconf2.0 + |compile_com(impconf2.0)|] == Ibranch(|compile_com(cifnotso)|) by
						{
							assert code_at(C,pc1 + |compile_bexp(b,d1,d0)| + d1,compile_com(cifso)) by { resolve_code_at(); }
						}
				
					assert compile_cont(C, impconf2.1, machconf2.0 + |compile_com(impconf2.0)|);
					
				}
				
			} else {

				assert (c2,k2,s2) == (cifnotso,k1,s1);

				assert code_at(C,pc1,compile_bexp(b,0,|code_ifso| + 1)) by { resolve_code_at(); }
				var machconf2 := (pc1 + |compile_bexp(b,d1,d0)| + d0, stk1, s1);
				assert transitions(C,machconf1,machconf2) by { compile_bexp_correct_false(C,str1,b,pc1,d1,d0,stk1); }
				assert star<configuration>(tr,machconf1,machconf2);

				assert code_at(C, machconf2.0, compile_com(impconf2.0)) by { resolve_code_at(); } 

				assert compile_cont(C,k1,pc1 + |compile_com(c1)|);
				assert k1 == k2;

				assert impconf2.2 == machconf2.2;
				assert machconf2.1 == [];
				
				assert compile_cont(C, impconf2.1, machconf2.0 + |compile_com(impconf2.0)|);
				assert match_config(C, impconf2, machconf2);
				
			}
			
		}
		
		case (WHILE(b, body), k) => {
			assert {:split_here} true;
			var tr := (c1,c2) => transition(C,c1,c2);
			
			var (c1,k1,s1) := impconf1;
			var (c2,k2,s2) := impconf2;
			var (pc1: nat,stk1,str1) := machconf1;

			var d1 := 0;
			var d0 := |compile_com(body)| + 1;

			if beval(s1,b) {

				assert code_at(C,pc1,compile_bexp(b,d1,d0)) by { resolve_code_at(); }
				var machconf2 := (pc1 + |compile_bexp(b,d1,d0)| + d1, [], s1);
				assert transitions(C,machconf1,machconf2) by { compile_bexp_correct_true(C,s1,b,pc1,d1,d0,stk1); }
				assert star<configuration>(tr,machconf1,machconf2);

				assert impconf2 == (body,Kwhile(b,body,k),s1);
				assert code_at(C,machconf2.0,compile_com(body)) by { resolve_code_at(); }
				
				assert compile_cont(C, impconf2.1, machconf2.0 + |compile_com(impconf2.0)|) by {

					var pc: nat := machconf2.0 + |compile_com(impconf2.0)|;
					var ofs: int := -( |compile_bexp(b,d1,d0)| + |compile_com(body)| + 1);
					assert C[pc] == Ibranch(ofs);
					var pc' := pc + 1 + ofs;
					var pc'' := pc' + |compile_com(WHILE(b, body))|;
					assert code_at(C,pc',compile_com(WHILE(b,body)));
					assert compile_cont(C, k, pc'');
					assert pc < |C|;
					assert pc' == pc1;
					assert pc'' == pc + 1;
					
					assert compile_cont(C, Kwhile(b,body,k), pc);

				}

				assert match_config(C,impconf2,machconf2);
				
				
			} else {

				assert code_at(C,pc1,compile_bexp(b,d1,d0)) by { resolve_code_at(); }
				var machconf2 := (pc1 + |compile_bexp(b,d1,d0)| + d0, [], s1);
				assert transitions(C,machconf1,machconf2) by { compile_bexp_correct_false(C,s1,b,pc1,d1,d0,stk1); }
				assert star<configuration>(tr,machconf1,machconf2);

				assert impconf2 == (SKIP,k,s1);

				assert compile_cont(C, k, machconf2.0);
				match_config_skip(C,k,s1,machconf2.0);
				
			}
			
		}
		
		case (SKIP, Kseq(c, k)) => {
			assert {:split_here} true;
			var tr := (c1,c2) => transition(C,c1,c2);
			
			var (c1,k1,s1) := impconf1;
			var (c2,k2,s2) := impconf2;
			var (pc1,stk1,str1) := machconf1;

			compile_cont_Kseq_inv(C,c,k,pc1,str1);
			var pc': nat :| star((c1,c2) => transition(C,c1,c2),(pc1, [], str1),(pc', [], str1)) && code_at(C,pc',compile_com(c)) && compile_cont(C,k,pc' + |compile_com(c)|);

			var machconf2: configuration := (pc',[],str1);
			assert star((c1,c2) => transition(C,c1,c2),machconf1,machconf2);

			assert match_config(C, impconf2, machconf2) by {
				assert impconf2.2 == machconf2.2;
				assert machconf2.1 == [];
				assert code_at(C, machconf2.0, compile_com(c2)) by { resolve_code_at(); } 
				assert compile_cont(C, k2, machconf2.0 + |compile_com(c2)|); 
				
			}
			
		}
		
		case (SKIP, Kwhile(b, c, k)) =>	{
			assert {:split_here} true;
			var tr := (c1,c2) => transition(C,c1,c2);
			
			var (c1,k1,s1) := impconf1;
			var (c2,k2,s2) := impconf2;
			var (pc1,stk1,str1) := machconf1;

			compile_cont_Kwhile_inv(C,b,c,k,pc1,str1);

			var pc': nat :| plus((c1,c2) => transition(C,c1,c2),(pc1, [], str1),(pc', [], str1)) && code_at(C,pc',compile_com(WHILE(b,c))) && compile_cont(C,k,pc' + |compile_com(WHILE(b,c))|);

			var machconf2: configuration := (pc', [], str1);
			assert plus((c1,c2) => transition(C,c1,c2),machconf1,machconf2);

			assert match_config(C, impconf2, machconf2) by {
				assert impconf2.2 == machconf2.2;
				assert machconf2.1 == [];
				assert code_at(C, machconf2.0, compile_com(c2)) by { resolve_code_at(); } 
				assert compile_cont(C, k2, machconf2.0 + |compile_com(c2)|); 
				
			}			
						
		}
		
	}
}

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
	requires star(step,(c,Kstop,s1),(SKIP,Kstop,s2))
	ensures machine_terminates(compile_program(c),s1,s2)
{
	var C := compile_program(c);
	var impconf1 := (c,Kstop,s1);
	var impconf2 := (SKIP,Kstop,s2);
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

lemma simulation_infseq_inv(C: code, impconf1: conf, machconf1: configuration)
	decreases measure(impconf1)
	requires infseq(step,impconf1)
	requires match_config(C,impconf1,machconf1)
	ensures exists impconf2: conf :: exists machconf2: configuration ::
	  infseq(step,impconf2)
		&& plus((c1,c2) => transition(C,c1,c2),machconf1,machconf2)
		&& match_config(C,impconf2,machconf2)
{
	
	var impconf2: conf :| step(impconf1,impconf2) && infseq(step,impconf2);
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
				infseq(step,impconf2)
				&& plus((c1,c2) => transition(C,c1,c2),machconfi,machconf2)
				&& match_config(C,impconf2,machconf2);

			star_plus_trans<configuration>((c1,c2) => transition(C,c1,c2),machconf1,machconfi,machconf2);
			
		}
		
}

predicate {:opaque} X(C: code, mc: configuration) {
	exists ic: conf :: infseq(step,ic) && match_config(C,ic,mc)
}
	
lemma compile_program_correct_diverging(c: com, s: store)
	requires H: infseq(step,(c,Kstop,s))
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
				assert exists ic: conf :: infseq(step,ic) && match_config(C,ic,a) by {
					reveal X();
				}
				var ic :| infseq(step,ic) && match_config(C,ic,a);
				simulation_infseq_inv(C,ic,a);
			}
		}
	}
	

	infseq_coinduction_principle_2((c1, c2) => transition(C,c1,c2),(mc) => X(C,mc),machconf1);
	
}
