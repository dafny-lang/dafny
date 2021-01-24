// RUN: %dafny /compile:0 "%s" > "%t"
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
