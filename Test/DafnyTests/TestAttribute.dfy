// RUN: %dafny /compileVerbose:1 /compile:0 /spillTargetCode:3 /noVerify "%s" > "%t"
// RUN: dotnet test -v:q -noLogo %S 2> %t.testresults.raw || true
// Remove the timestamp prefixes on the expected errors
// RUN: sed 's/[^]]*\]//' "%t".testresults.raw >> "%t"
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

class Even {
    var value:int;
    function method IsValid():bool reads this {
        this.value % 2 == 0
    }
    constructor (value:int) 
        requires value % 2 == 0
        ensures this.IsValid()
    {
        this.value := value;
    }
    function method Sum(a:int, b:int):int {
        a + b
    }
}

method {:extern} {:fresh} freshEven() returns (e:Even) ensures fresh(e)

method {:test} PassingTestUsingFresh() {
    var e:Even := freshEven();
    e.value := 4;
    expect(e.IsValid());
}

method {:test} FailingTestUsingFresh() {
    var e:Even := freshEven();
    e.value := 5;
    expect(e.IsValid());
}

method {:extern} {:mock} MockValidEven() returns (e:Even) 
    ensures fresh(e) 
    ensures e.IsValid() == true
method {:extern} {:mock} MockInValidEven() returns (e:Even) 
    ensures fresh(e) 
    ensures e.IsValid() == false

method {:test} PassingTestUsingValidMock() {
    var e:Even := MockValidEven();
    expect(e.IsValid());
}

method {:test} PassingTestUsingInValidMock() {
    var e:Even := MockInValidEven();
    expect(!e.IsValid());
}

method {:extern} {:mock} MockSum() returns (e:Even) 
    ensures fresh(e) 
    ensures e.Sum(2, 2) == 3

method {:test} PassingMockSum() {
    var e:Even := MockSum();
    expect(e.Sum(2, 2) == 3);
}

method {:extern} {:mock} MockSumForall() returns (e:Even) 
    ensures fresh(e) 
    ensures forall a:int, b:int :: e.Sum(a, b) == 3

method {:test} PassingMockForall() {
    var e:Even := MockSumForall();
    expect(e.Sum(2, 2) == 3);
    expect(e.Sum(3, 2) == 3);
}

method {:extern} {:mock} MockSumAsMultiplication() returns (e:Even) 
    ensures fresh(e) 
    ensures forall a:int, b:int :: e.Sum(a, b) == a * b
    
method {:test} PassingMockSumAsMultiplication() {
    var e:Even := MockSumAsMultiplication();
    expect(e.Sum(2, 2) == 4);
    expect(e.Sum(2, 3) == 6);
    expect(e.Sum(4, 0) == 0);
    expect(e.Sum(5, 1) == 5);
}

method {:extern} {:mock} MockSumWithArgumentMatcher() returns (e:Even) 
    ensures fresh(e) 
    ensures forall a:int, b:int :: (a > b) ==> (e.Sum(a, b) == a * b)
    ensures forall a:int, b:int :: (a <= b) ==> (e.Sum(a, b) == -a * b)
    
method {:test} PassingMockSumWithArgumentMatcher() {
    var e:Even := MockSumWithArgumentMatcher();
    expect(e.Sum(2, 2) == -4);
    expect(e.Sum(2, 3) == -6);
    expect(e.Sum(4, 0) == 0);
    expect(e.Sum(5, 1) == 5);
}

method {:extern} {:mock} MockField() returns (e:Even) 
    ensures fresh(e) 
    ensures e.value == 7;
    
method {:test} PassingMockField() {
    var e:Even := MockField();
    expect(e.value == 7);
    expect(e.value != 5);
}