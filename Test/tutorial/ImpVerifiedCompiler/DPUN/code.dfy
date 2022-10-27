module L1 {

	type state(!new)
	predicate transition(before: state, after: state)

}

module L2 {

	type state(!new)
	predicate transition(before: state, after: state)

}

module Smallstep {

	least predicate star<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T) {
		(conf1 == conf2) || (exists conf_inter: T :: R(conf1, conf_inter) && star(R,conf_inter, conf2))
	}
	
	lemma star_trans_sequent<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T, conf3: T)
		requires star(R,conf1,conf2) 
		requires star(R,conf2,conf3)
		ensures star(R,conf1,conf3)

	least predicate plus<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T) {
		(exists conf_inter: T :: R(conf1, conf_inter) && star(R,conf_inter, conf2))
	}
		
}

// Proof that one might which would go through, but doesn't

module Problem_1 {

	import L1
	import L2
	import opened Smallstep	

	predicate Match(a: L1.state, b: L2.state)

	lemma one_step(a1: L1.state, a2: L1.state, b1: L2.state)
		requires L1.transition(a1,a2)
		requires Match(a1,b1)
		ensures exists b2: L2.state :: star(L2.transition,b1,b2) && Match(a2,b2) 

	least lemma many_steps(a1: L1.state, a2: L1.state, b1: L2.state)
		requires star(L1.transition,a1,a2)
		requires Match(a1,b1)
		ensures exists b2: L2.state :: star(L2.transition,b1,b2) && Match(a2,b2)
	{
		if (a1 == a2) {
		} else {
			var ai :| L1.transition(a1,ai) && star(L1.transition,ai,a2);
			one_step(a1,ai,b1);
			var bi :| star(L2.transition,b1,bi) && Match(ai,bi); 
			many_steps(ai, a2, bi);
			var b2 :| star(L2.transition,bi,b2) && Match(a2,b2);
			star_trans_sequent(L2.transition,b1,bi,b2);
		}
	}
		
}

// First solution: reveal the least abstraction

module Problem_1_Solution_1 {

	import L1
	import L2
	import opened Smallstep	

	predicate Match(a: L1.state, b: L2.state)

	lemma one_step(a1: L1.state, a2: L1.state, b1: L2.state)
		requires L1.transition(a1,a2)
		requires Match(a1,b1)
		ensures exists b2: L2.state :: star(L2.transition,b1,b2) && Match(a2,b2)	

	lemma many_steps_prefix(k: ORDINAL, a1: L1.state, a2: L1.state, b1: L2.state)
		requires star#[k](L1.transition,a1,a2)
		requires Match(a1,b1)
		ensures exists b2: L2.state :: star(L2.transition,b1,b2) && Match(a2,b2)
	{
		if k.Offset != 0 {
			if a1 == a2 {
			} else {
				var ai :| L1.transition(a1,ai) && star#[k - 1](L1.transition,ai,a2);
				one_step(a1,ai,b1);
				var bi :| star(L2.transition,b1,bi) && Match(ai,bi); 
				many_steps_prefix(k - 1, ai, a2, bi);
				var b2 :| star(L2.transition,bi,b2) && Match(a2,b2);
				star_trans_sequent(L2.transition,b1,bi,b2);
			}
		}
	}

	lemma many_steps(a1: L1.state, a2: L1.state, b1: L2.state)
		requires star(L1.transition,a1,a2)
		requires Match(a1,b1)
		ensures exists b2: L2.state :: star(L2.transition,b1,b2) && Match(a2,b2)
	{
		var k :| star#[k](L1.transition,a1,a2);
		many_steps_prefix(k, a1, a2, b1);
	}
		
}

// Second solution, requires understanding solution 1, fool the rewriting with a name change

module Problem_1_Solution_2 {

	import L1
	import L2
	import opened Smallstep	

	predicate Match(a: L1.state, b: L2.state)

	lemma one_step(a1: L1.state, a2: L1.state, b1: L2.state)
		requires L1.transition(a1,a2)
		requires Match(a1,b1)
		ensures exists b2: L2.state :: star(L2.transition,b1,b2) && Match(a2,b2)

	predicate Star<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T) {
		star(R, conf1, conf2)
	}
		
	least lemma many_steps(a1: L1.state, a2: L1.state, b1: L2.state)
		requires star(L1.transition,a1,a2)
		requires Match(a1,b1)
		ensures exists b2: L2.state :: star(L2.transition,b1,b2) && Match(a2,b2)
	{
		if a1 == a2 {
		} else {
			var ai :| L1.transition(a1, ai) && star(L1.transition, ai, a2);
			one_step(a1, ai, b1);
			var bi :| Star(L2.transition, b1, bi) && Match(ai, bi); 
			many_steps(ai, a2, bi);
			assert exists b2: L2.state :: Star(L2.transition, bi, b2) && Match(a2, b2); 
			var b2 :| Star(L2.transition,bi,b2) && Match(a2,b2);
			star_trans_sequent(L2.transition,b1,bi,b2);
		}
	}

}

// Thrid solution, avoid the problem altogether with a different kind of abstraction

abstract module AbsSmallstep {

	type T(!new)

	predicate R(before: T,after: T)

	least predicate star(conf1: T, conf2: T) {
		(conf1 == conf2) || (exists conf_inter: T :: R(conf1, conf_inter) && star(conf_inter, conf2))
	}

	lemma star_trans_sequent(conf1: T, conf2: T, conf3: T)
		requires star(conf1,conf2) 
		requires star(conf2,conf3)
		ensures star(conf1,conf3)
		
}

module L1Sem refines AbsSmallstep {

	import opened L1
			
	type T(!new) = L1.state

	predicate R(before: T, after: T) {
			L1.transition(before,after)
	}
		
}

module L2Sem refines AbsSmallstep {

	import opened L2
		
	type T(!new) = L2.state
		
	predicate R(before: T, after: T) {
		L2.transition(before,after)
	}
	
}

module Problem_1_Solution_3 {

	import L1Sem
	import L2Sem
	
	predicate Match(a: L1Sem.T, b: L2Sem.T)

	lemma one_step(a1: L1Sem.T, a2: L1Sem.T, b1: L2Sem.T)
		requires L1Sem.R(a1,a2)
		requires Match(a1,b1)
		ensures exists b2: L2Sem.T :: L2Sem.star(b1,b2) && Match(a2,b2) 
	
	least lemma many_steps(a1: L1Sem.T, a2: L1Sem.T, b1: L2Sem.T)
		requires L1Sem.star(a1,a2)
		requires Match(a1,b1)
		ensures exists b2: L2Sem.T :: L2Sem.star(b1,b2) && Match(a2,b2)
	{
		if (a1 == a2) {
		} else {
			var ai :| L1Sem.R(a1,ai) && L1Sem.star(ai,a2);
			one_step(a1,ai,b1);
			var bi :| L2Sem.star(b1,bi) && Match(ai,bi); 
			many_steps(ai, a2, bi);
			var b2 :| L2Sem.star(bi,b2) && Match(a2,b2);
			L2Sem.star_trans_sequent(b1,bi,b2);
		}
	}	

}

module Problem_2 {

	import opened Smallstep
	
	predicate Prop<T(!new)>(R: (T,T) -> bool, a: T)

	lemma premise_1<T(!new)>(R: (T,T) -> bool, X: T -> bool, a : T)
		requires (forall a: T :: X(a) ==> exists b: T :: R(a,b) && X(b))
		requires X(a)
		ensures Prop(R,a)

	lemma premise_2<T(!new)>(R: (T,T) -> bool, X: T -> bool)
		requires (forall a: T :: X(a) ==> exists b: T :: plus(R,a, b) && X(b))
		ensures forall a: T :: (exists b: T :: star(R,a,b) && X(b)) ==> exists b: T :: R(a,b) && (exists c: T :: star(R,b,c) && X(c))
	
	lemma conclusion<T(!new)>(R: (T,T) -> bool, X: T -> bool, a : T)
		requires (forall a: T :: X(a) ==> exists b: T :: plus(R,a, b) && X(b))
		requires X(a)
		ensures Prop(R,a)
		// I have to comment because of timeout
	// {
	// 	var Y: T -> bool := (a: T) => exists b: T :: star(R,a,b) && X(b);
	// 	assert Y(a);
	// 	premise_2(R,X);
	// 	premise_1(R,Y,a);
	// }	

}

// Solution, need to investigate whether it can be simplified in this context

module Problem_2_Solution_1 {

	import opened Smallstep

	predicate Prop<T(!new)>(R: (T,T) -> bool, a: T)
		
	predicate {:opaque} PreReq_1<T(!new)>(R: (T,T) -> bool, X: T -> bool) {
		forall a: T :: X(a) ==> exists b: T :: R(a,b) && X(b)
	}

	lemma premise_1<T(!new)>(R: (T,T) -> bool, X: T -> bool, a : T)
		requires PreReq_1(R,X)
		requires X(a)
		ensures Prop(R,a)

	predicate {:opaque} PreReq_2<T(!new)>(R: (T,T) -> bool, X: T -> bool) {
		forall a: T :: X(a) ==> exists b: T :: plus(R,a, b) && X(b)
	}

	predicate {:opaque} Y<T(!new)>(R: (T,T) -> bool, X: T -> bool, a: T) {
		exists b: T :: star(R,a,b) && X(b)
	}

	lemma premise_2<T(!new)>(R: (T,T) -> bool, X: T -> bool)
		requires PreReq_2(R,X)
		ensures PreReq_1(R,(a: T) => Y(R,X,a))
	
	lemma conclusion<T(!new)>(R: (T,T) -> bool, X: T -> bool, a : T)
		requires H1: PreReq_2(R,X)
		requires H2: X(a)
		ensures Prop(R,a)
	{

		assert Y(R,X,a) by {
			reveal H2;
			reveal Y();
		}
	
		assert PreReq_1(R,(a: T) => Y(R,X,a)) by {
			reveal H1;
			premise_2(R,X);
		}
	
		premise_1(R,(a: T) => Y(R,X,a),a);

	}
		
}

// Note 1: depending on what this note is supposed to be, it might make sense to also
// go over the split_true for case analysis

// Note 2: extract examples of pain resulting from subset types

module Problem_3 {

	predicate P(pc: int)
		requires pc >= 0
	
	lemma premise_1()
		ensures exists pc': nat :: P(pc')
		
	lemma conclusion(pc: nat)
		ensures true
 	{

		premise_1();
		var pc' :| P(pc');

	}
		
}

module Problem_3_Solution_1 {

	predicate P(pc: int)
		requires pc >= 0
	
	lemma premise_1()
		ensures exists pc': nat :: P(pc')
		
	lemma conclusion(pc: nat)
		ensures true
 	{

		premise_1();
		var pc': nat :| P(pc');

	}
		
}


// This one is not inherently problematic, but a major source of instability and headaches
// solution is to type variable to catch difficulties ASAP
module Problem_4 {

	function f(x: int): int

	// Assume that Dafny can prove this on its own, but with some effort
	lemma f_pos(x: int)
		requires x >= 0
		ensures f(x) >= 0
	
	predicate P(x: nat, y: nat)

	lemma premise(x: int)
		requires x >= 0
		ensures exists y: nat :: P(x,y)

	lemma conclusion(C: seq<int>, pc: nat)
		ensures true
 	{

		var a: nat := 4;
		var b := f(a);
		premise(b); // It could fail here, or worse, figure it out
		var c :| P(b,c); // And now fail here, which can be tough to diagnose
		// Also, note that b could be one value inside a deeper structure
		
	}
		
}
