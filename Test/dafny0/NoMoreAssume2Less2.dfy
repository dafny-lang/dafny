// RUN: %exits-with 4 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file tests various ways of writing the equivalent of "assume false;" or "assert false;" inside a loop.
// It used to be that Dafny's translation of such statements into Boogie could cause Boogie to cut off the
// loop back edge, which would turn a loop into something that wasn't a loop. In particular, it would cause
// the expected "havoc loop_targets;" statement never to be generated, whose dramatic impact on what gets
// verified would be both mysterious and surprising to most Dafny users.
//
// The equally mysterious workaround for this problem used to be for Dafny users to replace their "assume false;"
// with something like "assume 2 < 2;", which Boogie wouldn't recognize in the same way.
//
// The current translation to Boogie makes sure that no user-supplied expression turns into exactly an
// "assume false;" or "assert false;". This means that Dafny users can use a statement like "assume false;"
// without chopping off back edges.
//
// It is still possible (in situations that would be rare in practice) to get some initially-surprising behavior
// from Boogie, because it is possible to introduce a "false" condition that will be detected by the control-flow
// handling in Boogie's abstract interpreter. Method Conjuncts4 below shows such an example.

method M0(n: nat) {
  var i := 0;
  while i < n {
    i := i + 1;
  }
  assert n == 0; // error
}

method M1(n: nat) {
  var i := 0;
  while i < n {
    assume false;
    i := i + 1;
  }
  assert n == 0; // error
}

method M2(n: nat) {
  var i := 0;
  while i < n {
    assume 2 < 2;
    i := i + 1;
  }
  assert n == 0; // error
}

method M3(n: nat) {
  var i := 0;
  while i < n {
    assert false; // error
    i := i + 1;
  }
  assert n == 0; // error
}

method M4(n: nat) {
  var i := 0;
  while i < n {
    assert 2 < 2; // error
    i := i + 1;
  }
  assert n == 0; // error
}

method M5(n: nat) {
  var i := 0;
  while i < n {
    assert false by { // error
    }
    i := i + 1;
  }
  assert n == 0; // error
}

ghost predicate P() { true }
ghost predicate Q() { true }
ghost predicate R(n: nat) { true }
ghost predicate False() { false }

method Conjuncts0(n: nat) {
  var i := 0;
  while i < n {
    assume P() && false && Q();
    i := i + 1;
  }
  assert n == 0; // error
}

method Conjuncts1(n: nat) {
  var i := 0;
  while i < n {
    assert P() && false && Q(); // error
    i := i + 1;
  }
  assert n == 0; // error
}

method Conjuncts2(n: nat) {
  var i := 0;
  while i < n {
    assume False();
    i := i + 1;
  }
  assert n == 0; // error
}

method Conjuncts3(n: nat) {
  var i := 0;
  while i < n {
    assert False(); // error
    i := i + 1;
  }
  assert n == 0; // error
}

method Conjuncts4(n: nat, m: nat) {
  var i := 0;
  while i < n {
    assert R(m) && false; // error
    i := i + 1;
  }
  // The following assertion is provable, because the "false" in the assertion above
  // gets noticed by Boogie's abstract interpreter, which then (correctly) figures out
  // that no control leads from inside the loop back to the loop head. Therefore, it
  // infers the loop invariant i == 0.
  // It takes a special (and unusual) condition to get this behavior. This example
  // uses two conjuncts, one of which is "false" and one of which is a non-Lit expression.
  assert n == 0;
}

method LoopInvariants(n: nat) {
  var i := 0;
  while i < n {
    for j := 0 to 5
      invariant false // error
    {
    }
    i := i + 1;
  }
  assert n == 0; // error
}

method Calls0(n: nat) {
  var i := 0;
  while i < n {
    FalsePre(); // error
    i := i + 1;
  }
  assert n == 0; // error
}

method Calls1(n: nat) {
  var i := 0;
  while i < n {
    FalsePost();
    i := i + 1;
  }
  assert n == 0; // error
}

method FalsePre()
  requires false

method FalsePost()
  ensures false

method LabeledExpressions0(n: nat)
  requires A: false
{
  var i := 0;
  while i < n {
    reveal A;
    i := i + 1;
  }
  assert n == 0; // error
}

method LabeledExpressions1(n: nat)
{
  assert A: false; // error
  var i := 0;
  while i < n {
    reveal A;
    i := i + 1;
  }
  assert n == 0; // error
}

method LabeledExpressions2(n: nat)
{
  assert A: false by { // error
  }
  var i := 0;
  while i < n {
    reveal A;
    i := i + 1;
  }
  assert n == 0; // error
}
