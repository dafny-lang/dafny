// RUN: %dafny /out:Output/DafnyMain.cs TestAttribute.dfy /compile:0 /spillTargetCode:3 /noVerify
// RUN: dotnet test -v:q -noLogo 2>%t.raw || true
// Remove the timestamp prefixes on the expected errors
// RUN: sed 's/[^]]*\]//' "%t".raw > "%t"
// RUN: %diff "%s.expect" "%t"

include "../exceptions/VoidOutcomeDt.dfy"
include "../exceptions/NatOutcomeDt.dfy"

function method SafeDivide(a: nat, b: nat): NatOutcome {
  if b == 0 then
    NatFailure("Divide by zero")
  else
    NatSuccess(a/b)
}

method UnsafeDivide(a: nat, b: nat) returns (r: nat) {
  expect b != 0;
  return a/b;
}

method FailUnless(p: bool) returns (r: VoidOutcome) ensures r.VoidSuccess? ==> p {
  if p {
    return VoidSuccess;
  } else {
    return VoidFailure("requirement failed");
  }
}

function method {:test} PassingTest(): VoidOutcome {
  VoidSuccess
}

function method {:test} FailingTest(): VoidOutcome {
  VoidFailure("Whoopsie")
}

method {:test} PassingTestUsingExpect() {
  expect 2 + 2 == 4;
}

method {:test} FailingTestUsingExpect() {
  expect 2 + 2 == 5;
}

method {:test} FailingTestUsingExpectWithMessage() {
  expect 2 + 2 == 5, "Down with DoubleThink!";
}

method {:test} PassingTestUsingAssignOrHalt() {
  var x := 5;
  var y := 2;
  var q :- expect SafeDivide(x, y);
  expect q == 2;
}

method {:test} FailingTestUsingAssignOrHalt() {
  var x := 5;
  var y := 0;
  var q :- expect SafeDivide(x, y);
}

method {:test} PassingTestUsingNoLHSAssignOrHalt() {
  :- expect FailUnless(true);
}

method {:test} FailingTestUsingNoLHSAssignOrHalt() {
  :- expect FailUnless(false);
}

method {:test} PassingTestThatReturnsAFailureIncompatibleValue() returns (i:int) {
 return 0;
}

class Value {
    var i:int;
    // A constructor that can cause an exception in the target language if used in a context not verified by Dafny
    constructor(i:int) requires i != 0 {
        this.i := 0/i;
    }
}

method {:test} PassingTestThatUsesMocks(v:Value) modifies v {
    v.i := 0;
}

