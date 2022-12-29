// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module ExampleA {
  export
    provides Test

  trait C {
    predicate F()
      ensures false
  }

  predicate BadGhost()
    ensures false
  {
    // regression: in the the following line, the verifier once used the fact that all types were nonempty
    var c: C :| true;  // error: cannot prove existence of such a "c"
    c.F()
  }

  method Test() {
    ghost var p := BadGhost();
    var x := 3 / 0;  // no complaint, given the postcondition of BadGhost
  }
}

module ExampleA_Compiled {
  trait C {
    predicate method F()
      ensures false
  }

  predicate method BadCompiled()
    ensures false
  {
    // regression: the verifier used to verify the next line (though the compiler then complained it didn't know how to generate code)
    var c: C :| true;  // error: cannot prove existence of such a "c"
    c.F()
  }
}

module ExampleB {
  export
    provides Test

  trait D {
    lemma False()
      ensures false
  }

  lemma BadGhost()
    ensures false
  {
    var d: D;   // regression: the verifier once thought the compiler would provide a value for "d"
    d.False();  // error: d is used before it is assigned
  }

  lemma BadSuchThatGhost()
    ensures false
  {
    // regression: the verifier once thought the compiler would provide a value for "d"
    var d: D :| d == d;  // error: cannot prove existence of such a "d"
    d.False();
  }

  method BadCompiled()
    ensures false
  {
    // regression: the verifier used to verify the next line (though the compiler then complained it didn't know how to generate code)
    var d: D :| d == d;  // error: cannot prove existence of such a "d"
    d.False();
  }

  method Test() {
    if * {
      BadGhost();
    } else {
      BadCompiled();
    }
    var x := 3 / 0;
  }
}

method Main() {
  // regression: without the two BadCompiled() methods above, this entire program used to verify and
  // compile, but it would then crash when run; this has since been fixed.
  if * {
    ExampleA.Test();
  } else {
    ExampleB.Test();
  }
}

module ExampleC {
  trait D {
    lemma False()
      ensures false
  }

  lemma Fine0(d: D)  // this is like a precondition of "false"
    ensures false
  {
    d.False();
  }

  lemma Fine1(s: set<D>)
    requires s != {}  // this is like a precondition of "false"
    ensures false
  {
    var d: D :| d in s;
    d.False();
  }

  lemma IfCase() {
    if
    case d: D :| d == d =>
      d.False();
      assert false;  // fine, since control will never reach this point
    case true =>
  }
}

module ExampleD {
  type D

  method Test() {
    var d0: D :| true;  // error: cannot prove existence of a D here
    var d1: D :| true;  // here, it can prove the existence of a D, since "d0" is one such value
  }
}

module OtherBindersInStatements {
  type Opaque {
    lemma False()
      ensures false
  }
  trait C {
    lemma False()
      ensures false
  }

  method Forall0()
  {
    var b := forall c: Opaque :: (c.False(); 5/0 == 19);  // fine, since the lemma helps figure out that "c: Opaque" is an impossibility
    var x := 40 / 0;  // error: division by zero (the call to c.False() on the line above
  }

  method Forall1()
  {
    var b := forall c: C :: (c.False(); 5/0 == 19);  // fine, since the lemma helps figure out that "c: C" is an impossibility
    var x := 40 / 0;  // error: division by zero (the call to c.False() on the line above
  }

  method Exists()
  {
    var b := exists c: C :: (c.False(); 5/0 == 19);  // fine, since the lemma helps figure out that "c: C" is an impossibility
    var x := 40 / 0;  // error: division by zero (the call to c.False() on the line above
  }

  method SetComprehension0()
  {
    var b := set c: C | (c.False(); 5/0 == 19);  // fine, since the lemma helps figure out that "c: C" is an impossibility
    var x := 40 / 0;  // error: division by zero (the call to c.False() on the line above
  }

  method SetComprehension1()
  {
    var b := set c: C | true :: (c.False(); 5/0 == 19);  // fine, since the lemma helps figure out that "c: C" is an impossibility
    var x := 40 / 0;  // error: division by zero (the call to c.False() on the line above
  }

  method MapComprehension0()
  {
    var b := map c: C | (c.False(); 5/0 == 19) :: 102;  // fine, since the lemma helps figure out that "c: C" is an impossibility
    var x := 40 / 0;  // error: division by zero (the call to c.False() on the line above
  }

  method MapComprehension1()
  {
    var b := map c: C | true :: (c.False(); 5/0 == 19);  // fine, since the lemma helps figure out that "c: C" is an impossibility
    var x := 40 / 0;  // error: division by zero (the call to c.False() on the line above
  }

  method MapComprehension2()
  {
    var b := map c: C | true :: (c.False(); 5/0 == 19) := 20;  // fine, since the lemma helps figure out that "c: C" is an impossibility
    var x := 40 / 0;  // error: division by zero (the call to c.False() on the line above
  }

  method MapComprehension3()
  {
    var b := imap c: C | true :: 20 := (c.False(); 5/0 == 19);  // fine, since the lemma helps figure out that "c: C" is an impossibility
    var x := 40 / 0;  // error: division by zero (the call to c.False() on the line above
  }

  method Lambda()
  {
    var f := (c: C) => (c.False(); 5/0 == 19);  // fine, since the lemma helps figure out that "c: C" is an impossibility
    var x := 40 / 0;  // error: division by zero (the call to c.False() on the line above
  }
}

module OtherBindersInExpressions {
  type C(!new) {
    lemma False()
      ensures false
  }

  function Forall0(): int
  {
    var b := forall c: C :: 5/0 == 19;  // error: division by zero
    40
  }

  function Forall1(): int
  {
    var b := forall c: C :: (c.False(); 5/0 == 19);  // fine, since the lemma helps figure out that "c: C" is an impossibility
    40 / 0  // error: division by zero (the call to c.False() on the line above
  }

  function Forall2(): int
  {
    var b := forall c: C :: (c.False(); 5/0 == 19);  // fine, since the lemma helps figure out that "c: C" is an impossibility
    40 / 0  // error: division by zero (the call to c.False() on the line above
  }

  function Forall3(): int
  {
    var b := forall c: C :: (c.False(); 5/0 == 19);  // fine, since the lemma helps figure out that "c: C" is an impossibility
    40 / 0  // error: division by zero (the call to c.False() on the line above
  }

  function Exists(): int
  {
    var b := exists c: C :: (c.False(); 5/0 == 19);  // fine, since the lemma helps figure out that "c: C" is an impossibility
    40 / 0  // error: division by zero (the call to c.False() on the line above
  }

  function SetComprehension0(): int
  {
    var b := iset c: C | (c.False(); 5/0 == 19);  // fine, since the lemma helps figure out that "c: C" is an impossibility
    40 / 0  // error: division by zero (the call to c.False() on the line above
  }

  function SetComprehension1(): int
  {
    var b := set c: C | true :: (c.False(); 5/0 == 19);  // fine, since the lemma helps figure out that "c: C" is an impossibility
    40 / 0  // error: division by zero (the call to c.False() on the line above
  }

  function MapComprehension0(): int
  {
    var b := imap c: C | (c.False(); 5/0 == 19) :: 102;  // fine, since the lemma helps figure out that "c: C" is an impossibility
    40 / 0  // error: division by zero (the call to c.False() on the line above
  }

  function MapComprehension1(): int
  {
    var b := imap c: C | true :: (c.False(); 5/0 == 19);  // fine, since the lemma helps figure out that "c: C" is an impossibility
    40 / 0  // error: division by zero (the call to c.False() on the line above
  }

  function MapComprehension2(): int
  {
    var b := map c: C | true :: (c.False(); 5/0 == 19) := 20;  // fine, since the lemma helps figure out that "c: C" is an impossibility
    40 / 0  // error: division by zero (the call to c.False() on the line above
  }

  function MapComprehension3(): int
  {
    var b := imap c: C | true :: 20 := (c.False(); 5/0 == 19);  // fine, since the lemma helps figure out that "c: C" is an impossibility
    40 / 0  // error: division by zero (the call to c.False() on the line above
  }

  function Lambda(): int
  {
    var f := (c: C) => (c.False(); 5/0 == 19);  // fine, since the lemma helps figure out that "c: C" is an impossibility
    40 / 0  // error: division by zero (the call to c.False() on the line above
  }
}
