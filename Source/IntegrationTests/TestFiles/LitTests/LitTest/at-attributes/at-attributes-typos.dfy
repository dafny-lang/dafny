// RUN: %baredafny resolve "%s" > "%t"
// RUN: %diff "%t" "%s.check"
// Attributes on top-level declarations

@AutoContract // Should be AutoContracts
class A {
  predicate Valid() {
    true
  }
}

@Native // Should be NativeType
newtype ubyte = x : int | 0 <= x < 256

@Native(native := false) // Should be NativeType
newtype ubyte3 = x : int | 0 <= x < 256

@External // Should be Extern
method ExternTest()

@DisableNonLinearArithmetic // Should be DisableNonlinearArithmetic
@Option("--function-syntax:3") // Should be Options
module SimpleLinearModule {
  class Test {
    static @IsolateAssertions function Test(): int { 3 } // At-Attributes not after keywords
  }
}

/// Attributes on functions and methods

codatatype Stream = Stream(i: int, tail: Stream) {
  @ABstemious // Should be Abstemious
  function Constant(): int { 1 }
}

function f(x:int) : bool
  requires x > 3
{
  x > 7
}

@AutoReq // Should be AutoRequires
@AutorevealDependenciesAll(false) // Should be Auto_R_eveal...
@AutorevealDependenciesAll(true)
@AutorevealDependencies(level := 10)
@axiom // Should be Axiom
@Compilation(true) // Should be Compile
@Fuels(low := 1) // Should be Fuel
@Fuels(low := 1, high := 2)
@ID("G#1") // Should be Id
function g(y:int, b:bool) : bool
{
  if b then f(y + 2) else f(2*y)
}
// TODO continue from https://dafny.org/latest/DafnyRef/DafnyRef#1122-autoreq

@concurrent // Should be Concurrent
method ConcurrentMethod()
  reads {}
  modifies {}
{
}

@Isolation // Should be IsolateAssertions
method Test(a: int, b: int, c: int)
  requires a < b && b < c
{
  @Splithere // Should be SplitHere
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
  ensures forall n: nat @inductive(n) @triggers(NatToUnary(n)) :: UnaryToNat(NatToUnary(n)) == n
  // Should be induction and trigger
{
}

@only        // Should be Only 
@print       // Should be Print
@priority(2) // Should be Priority
@RLimit(1000) // Should be ResourceLimit
@Selectivechecking // Should be SelectiveChecking
@TLimit(1000) // Should be TimeLimit
@TLimitMultiplier(2) // Should be TimeLimitMultiplier
method VerifyThisOnly() {
  print "hello";
  @StartcheckingHere // Should be StartCheckingHere
  assert true;
}

@TailRecursive // Should be TailRecursion
@Transperent // Should be Transparent
function Fib(n: nat, a: int, b: int): int {
  if n == 0 then b
  else Fib(n - 1, b, a + b)
}

@NoVerify      // Should be Verify(false)
@Tests         // Should be Test
@VcMaxCost(10) // SHould be Vcs...
@VcMaxKeepGoingSplits(10)
@VcMaxSplits(10)
@IsolateAssertion // Should be IsolateAssertion
method TestItAll() {
  expect true;
}

@Synthesizes // Should be Synthesize
method Synthesizing(x: int) returns (y: int)
  ensures x == y + 1

// Attributes on reads and modifies clauses

@concurrent // Should be Concurrent
method Test(a: A)
  @Assumeconcurrent reads a // Should be AssumeConcurrent
  @Assumeconcurrent modifies a
  @error("Error Message") // Should be Error
  requires a != null
{
  @Split // Should be SplitHere
  @Subsumption(0) // Should be SubSumption
  assert true;                  // Unchecked
  @OnlyAfer // Should be OnlyAfter
  assert true;
  @Focuses assert true; // Should be Focus
  @OnlyBefre // Should be OnlyBefore
  assert true; // Checked
  if false {
    @Oly // Should be Only
    @Contradicts // Should be Contradiction
    assert false;
  }
  @assumption // Should be assumption
  ghost var b := b && true;

}



