 module Setup {

	type t(00)

	predicate A()
	predicate B()
	predicate C()
	predicate P(x: t)

	ghost const k: t

}

module implication_1 {

	import opened Setup

	lemma conclusion()
		ensures A() ==> (B() ==> A())
	{
	}

}

module implication_2 {

	import opened Setup

	lemma conclusion()
		ensures (A() ==> (B() ==> C())) ==> ((A() ==> B()) ==> (A() ==> C()))
	{
	}

}

module implication_3 {

	import opened Setup

	lemma conclusion()
		ensures (forall x: t :: A() ==> P(x)) ==> (A() ==> forall x: t :: P(x))
	{
	}
	
}

module conjunction_1 {

	import opened Setup

	lemma conclusion()
		ensures (A() && B()) ==> A()
	{
	}

}

module conjunction_2 {

	import opened Setup

	lemma conclusion()
		ensures (A() && B()) ==> B()
	{
	}

}

module conjunction_3 {

	import opened Setup

	lemma conclusion()
		ensures A() ==> B() ==> A() && B()
	{
	}
	
}

module disjunction_1 {

	import opened Setup

	lemma conclusion()
		ensures A() ==> (A() || B())
	{
	}

}

module disjuction_2 {

	import opened Setup

	lemma conclusion()
		ensures B() ==> (A() || B())
	{
	}

}

module disjunction_3 {

	import opened Setup

	lemma conclusion()
		ensures (A() || B()) ==> ((A() ==> C()) ==> ((B() ==> C()) ==> C()))
	{
	}
	
}

module false_1 {

	import opened Setup

	lemma conclusion()
		ensures A() ==> (! A() ==> false)
	{
	}
		
}

module false_2 {

	import opened Setup

	lemma conclusion()
		ensures (A() ==> false) ==> ! A()
	{
	}
		
}

module false_3 {

	import opened Setup

	lemma conclusion()
		ensures false ==> A()
	{
	}
		
}

module universal {

	import opened Setup
	
	lemma conclusion()
		ensures (forall x: t :: P(x)) ==> P(k)
	{
	}
		
}

module existensial {

	import opened Setup

	lemma conclusion()
		ensures P(k) ==> exists x: t :: P(x)
	{
	}

}

module existensial_universal {

	import opened Setup

	lemma conclusion()
		ensures (exists x: t :: P(x)) ==> ((forall x: t :: P(x) ==> B()) ==> B())
	{
	}

}

module axiom {

	import opened Setup

	lemma premise()
		ensures A()

	lemma conclusion()
		ensures A()
	{
		premise();
	}
		
}

module modus_ponens {

	import opened Setup

	lemma premise_1()
		ensures A() ==> B()

	lemma premise_2()
		ensures A()

	lemma conclusion()
		ensures B()
	{
		premise_1();
		premise_2();
	}
		
}

module generalization {

	import opened Setup

	lemma premise(x: t)
		ensures P(x)

	lemma conclusion()
		ensures forall x: t :: P(x)
	{
		forall x { premise(x); }
	}
		
}
