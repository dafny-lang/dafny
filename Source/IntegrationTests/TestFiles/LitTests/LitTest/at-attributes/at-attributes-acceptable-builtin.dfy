// RUN: %baredafny resolve "%s"
// Attributes on top-level declarations

@AutoContracts
class A {
  predicate Valid() {
    true
  }
}

@NativeType
newtype ubyte = x : int | 0 <= x < 256

@NativeType(native := true) // This is the default
newtype ubyte2 = x : int | 0 <= x < 256

@NativeType(native := false)
newtype ubyte3 = x : int | 0 <= x < 256

@NativeType(name := "byte")
newtype ubyte4 = x : int | 0 <= x < 256

@Extern
method ExternTest()

@Extern(name := "MyFunction")
method ExternTest2()

@Extern(moduleName := "MyModule", name := "MyFunction")
method ExternTest3()

@DisableNonlinearArithmetic
@Options("--function-syntax:3")
module SimpleLinearModule {
}

/// Attributes on functions and methods

codatatype Stream = Stream(i: int, tail: Stream) {
  @Abstemious
  function Constant(): int { 1 }
}

function f(x:int) : bool
  requires x > 3
{
  x > 7
}

@AutoRequires
@AutoRevealDependenciesAll(false)
@AutoRevealDependenciesAll(true)
@AutoRevealDependencies(level := 10)
@Axiom
@Compile(true)
@Fuel(low := 1)
@Fuel(low := 1, high := 2)
@Id("G#1")
function g(y:int, b:bool) : bool
{
  if b then f(y + 2) else f(2*y)
}
// TODO continue from https://dafny.org/latest/DafnyRef/DafnyRef#1122-autoreq

@Concurrent
method ConcurrentMethod()
  reads {}
  modifies {}
{
  @Fuel(functionName := "g", low := 2, high := 3)
  assert g(1, 0) == 2;
}

@IsolateAssertions
method Test(a: int, b: int, c: int)
  requires a < b && b < c
{
  @SplitHere
  assert a < c; 
  assert c > a;
}

datatype Unary = Zero | Succ(Unary)

function UnaryToNat(n: Unary): nat {
  match n
  case Zero => 0
  case Succ(p) => 1 + UnaryToNat(p)
}

function NatToUnary(n: nat): Unary {
  if n == 0 then Zero else Succ(NatToUnary(n - 1))
}

lemma Correspondence()
  ensures forall n: nat @induction(n) @trigger(NatToUnary(n)) :: UnaryToNat(NatToUnary(n)) == n
{
}

@Only
@Print
@Priority(2)
@ResourceLimit(1000)
@SelectiveChecking
@TimeLimit(1000)
@TimeLimitMultiplier(2)
method VerifyThisOnly() {
  print "hello";
  @StartCheckingHere
  assert true;
}

@TailRecursion
@Transparent
function Fib(n: nat, a: int, b: int): int {
  if n == 0 then b
  else Fib(n - 1, b, a + b)
}

@Verify
@Test
@VcsMaxCost(10)
@VcsMaxKeepGoingSplits(10)
@VcsMaxSplits(10)
@IsolateAssertions
method TestItAll() {
  expect true;
}

@Synthesize
method Synthesizing(x: int) returns (y: int)
  ensures x == y + 1

// Attributes on reads and modifies clauses

@Concurrent
method Test(a: A)
  @AssumeConcurrent reads a
  @AssumeConcurrent modifies a
  @Error("Error Message")
  requires a != null
  @Error("Error Message", "Success Message")
  requires a != null
{
  @SplitHere
  @SubSumption(0)
  assert true;                  // Unchecked
  @OnlyAfter
  assert true;
  @Focus assert true;
  @OnlyBefore
  assert true; // Checked
  if false {
    @Only
    @Contradiction
    assert false;
  }
  @Assumption
  ghost var b := b && true;

}



