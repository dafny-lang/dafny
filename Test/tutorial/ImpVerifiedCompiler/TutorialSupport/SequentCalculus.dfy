module Setup {

	type t(00)

	predicate A()
	predicate B()
	predicate C()
	predicate P(x: t)

	ghost const k: t

}

module axiom {

	import opened Setup
		
	lemma conclusion()
		requires A()
		ensures A()
	{
	}

}

module cut {

	import opened Setup

	lemma premise_1()
		ensures A()

	lemma premise_2()
		requires A()
		ensures B()

	lemma conclusion()
		ensures B()
	{
		premise_1();
		premise_2();
	}

		
}

module weakening {

	import opened Setup

	lemma premise()
		ensures A()

	lemma conclusion()
		requires B()
		ensures A()
	{
		premise();
	}
	
}

module permutation {

	import opened Setup

	lemma premise()
		requires A()
		requires B()
		ensures C()

	lemma conclusion()
		requires B()
		requires A()
		ensures C()
	{
		premise();
	}

}

module contraction {

	import opened Setup

	lemma premise()
		requires A()
		requires A()
		ensures B()
		
	lemma conclusion()
		requires A()
		requires A()
		ensures B()
	{
		premise();
	}

}

module conjunction_right {

	import opened Setup
		
	lemma premise_1()
		ensures A()

	lemma premise_2()
		ensures B()

	lemma conclusion()
		ensures A() && B()
	{
		premise_1();
		premise_2();
	}

}

module conjunction_left {

	import opened Setup
		
	lemma premise_1()
		ensures A()

	lemma premise_2()
		ensures B()

	lemma conclusion()
		ensures A() && B()
	{
		premise_1();
		premise_2();
	}

}

module disjunction_right_1 {

	import opened Setup

	lemma premise()
		ensures A()

	lemma conclusion()
		ensures A() || B()
	{
		premise();
	}
		
}

module disjunction_right_2 {

	import opened Setup

	lemma premise()
		ensures B()

	lemma conclusion()
		ensures A() || B()
	{
		premise();
	}
		
}

module disjunction_left {

	import opened Setup

	lemma premise_1()
		requires A()
		ensures C()

	lemma premise_2()
		requires B()
		ensures C()
		
	lemma conclusion()
		requires A() || B()
		ensures C()
	{
		if A() {
				premise_1();
		}
		else {
				premise_2();
			}
	}
		
}	

module implication_right {

	import opened Setup
	
	lemma premise()
		requires A()
		ensures B()

		lemma conclusion()
			ensures A() ==> B()
		{
			if A() {
				premise();
			}
		}

}

module implication_left {

	import opened Setup
	
	lemma premise_1()
		ensures A()

	lemma premise_2()
		requires B()
		ensures C()
		
	lemma conclusion()
		requires A() ==> B()
		ensures C()
	{
		premise_1();
		premise_2();
	}

}

module negation_right {

	import opened Setup

	lemma premise()
		requires A()
		ensures false

	lemma conclusion()
		ensures ! A()
	{
		if A() {
			premise();
		}
	}
		
}

module negation_left {

	import opened Setup

	lemma premise()
		ensures A()

	lemma conclusion()
		requires ! A()
		ensures B()
	{
		premise();
	}
	
}

module false_left {

	import opened Setup

	lemma conclusion()
		requires false
		ensures A()
	{
	}
	
}

module universal_right {

	import opened Setup
	
	lemma premise(x: t)
		ensures P(x)

	lemma conclusion()
		ensures forall x: t :: P(x)
	{
		forall x { premise(x); }
	}

}

module universal_left {

	import opened Setup
	
	lemma premise()
		requires P(k)
		ensures B()

	lemma conclusion()
		requires forall x: t :: P(x)
		ensures B()
	{
		premise();
	}

}

module existential_right {

	import opened Setup

	lemma premise()
		ensures P(k)
		
	lemma conclusion()
		ensures exists x: t :: P(x)
	{
		premise();
	}
		
}

module existential_left {

	import opened Setup

	lemma premise(x: t)
		requires P(x)
		ensures B()

	lemma conclusion()
		requires exists x: t :: P(x)
		ensures B()
	{
		var x :| P(x);
		premise(x);
	}

}
