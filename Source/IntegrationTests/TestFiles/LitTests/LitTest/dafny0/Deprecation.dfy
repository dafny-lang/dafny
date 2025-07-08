// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --allow-warnings --relax-definite-assignment

// This file contains tests for messags about various deprecated features.
// As those features go away completely, so can the corresponding tests.

method Main() {
  // Test that we get all the way to compilation, despite the deprecation warnings below
  print "yet here we are\n";
}

// ----------

class C {
  constructor ()
    modifies this  // deprecation warning: "this" is no longer needed in modifies of a constructor
  {
  }
}

// ----------

inductive predicate InductivePredicate()  // deprecation warning: "inductive predicate" has been renamed to "least predicate"
{ true }

copredicate CoPredicate()  // deprecation warning: "copredicate" has been renamed to "greatest predicate"
{ true }

inductive lemma InductiveLemma()  // deprecation warning: "inductive lemma" has been renamed to "least lemma"
{ }

colemma CoLemma()  // deprecation warning: "colemma" has been renamed to "greatest lemma"
{ }

// ------- empty forall statement and forall statement with parentheses -----------------------------------------

class EmptyForallStatement {
  var data: int

  ghost predicate P(x: int)

  lemma EstablishP(x: int)
    ensures P(x)

  method EmptyForall0()
    modifies this
    ensures data == 8
  {
    forall () { // warning (x2): forall statement with no bound variables, and forall statement with parentheses
      this.data := 8;
    }
  }

  method EmptyForall1()
    ensures P(8)
  {
    forall { // warning: forall statement with no bound variables
      EstablishP(8);
    }
  }

  method EmptyForall2(s: set<EmptyForallStatement>)
    ensures forall x :: x in s ==> P(x.data)
  {
    forall (x | x in s) { // warning: forall statement with parentheses
      EstablishP(x.data);
    }
  }

  method EmptyForall3(s: set<EmptyForallStatement>)
    ensures forall x <- s :: P(x.data)
  {
    forall (x <- s) // warning: forall statement with parentheses
      ensures P(x.data)
    {
      EstablishP(x.data);
    }
  }

  method EmptyForall4()
  {
    forall // warning: forall statement with no bound variables
      ensures exists k :: P(k)
    {
      var y := 8;
      assume P(y);
    }
    assert exists k :: P(k); // yes
  }
}
