// RUN: %exits-with 2 %verify --type-system-refresh=false --general-newtypes=false "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Common {
  datatype FailureCompatible = Make { // Extract is ghost
    predicate IsFailure() { true }
    function PropagateFailure(): real { 12.0 }
    ghost function Extract(): real { 9.0 }
  }

  datatype FailureCompatible2 = Make { // PropagateFailure is ghost
    predicate IsFailure() { true }
    ghost function PropagateFailure(): real { 12.0 }
    function Extract(): real { 9.0 }
  }

  datatype FailureCompatible3 = Make { // IsFailure is ghost
    ghost predicate IsFailure() { true }
    function PropagateFailure(): real { 12.0 }
    function Extract(): real { 9.0 }
  }

  method M() returns (r: FailureCompatible) { }
  method M2() returns (r: FailureCompatible2) { }
  method M3() returns (r: FailureCompatible3) { }
}

module Test0 {
  import opened Common

  method N() returns (ghost s: real) {
    var ss: real;
    ss :- M2(); // OK
    ss :- M(); // ERROR - Extract is ghost assigning to non-ghost ss
  }
}

module Test1 {
  import opened Common

  method N1() returns (s: real) {
    ghost var ss: real;
    ss :- M(); // OK
    ss :- M2(); // ERROR - PropagateFailure is ghost assigning to non-ghost s
  }
}

module Test2 {
  import opened Common

  method N2() returns (ghost s: real) {
    ghost var ss: real;
    ss :- M(); // OK
    ss :- M2(); // OK
    ss :- M3(); // ERROR - IsFailure is ghost, guarding return-control-flow in non-ghost method
  }
}

module Test3 {
  import opened Common

  method NN() returns (ghost s: real) {
    // The following two statements cause the auto-ghost s0 and s1 to become ghost and non-ghost, respectively.
    var s0 :- M();
    var s1 :- M2();
    // Next, we test that s0 is really ghost and s1 is really non-ghost
    ghost var g := 3.0;
    s0 := g; // verifying s0 is non-ghost
    print s1, "\n"; // verifying s1 is non-ghost
  }
}

module MoreTests {
  datatype NotFunctionsAtAll = Make(PropagateFailure: () -> char)
  {
    const IsFailure: () -> bool
    const Extract: () -> real
  }

  method Client() returns (r: char) {
    var e: NotFunctionsAtAll;
    var x :- e;
  }
}
