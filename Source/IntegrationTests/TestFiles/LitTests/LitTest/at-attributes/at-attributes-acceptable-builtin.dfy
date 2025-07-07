// RUN: %resolve "%s"
// Attributes on top-level declarations

@AutoContracts
class A {
  ghost var Repr: set<object>

  var x: int

  var y: int

  predicate Valid() {
    true
  }
}

@NativeIntOrReal
newtype ubyte = x : int | 0 <= x < 256

@NativeInt
newtype ubyte2 = x : int | 0 <= x < 256

@NativeNone
newtype ubyte3 = x : int | 0 <= x < 256

@NativeUInt8
newtype ubyte4 = x : int | 0 <= x < 256

@NativeInt8
newtype ubyte5 = x : int | 0 <= x < 100

@NativeUInt16
newtype ubyte6 = x : int | 0 <= x < 256

@NativeInt16
newtype ubyte7 = x : int | 0 <= x < 256

@NativeUInt32
newtype ubyte8 = x : int | 0 <= x < 256

@NativeInt32
newtype ubyte9 = x : int | 0 <= x < 256

//@NativeInt53
//newtype ubyte10 = x : int | 0 <= x < 256

@NativeUInt64
newtype ubyte11 = x : int | 0 <= x < 256

@NativeInt64
newtype ubyte12 = x : int | 0 <= x < 256

//@NativeUInt128
//newtype ubyte13 = x : int | 0 <= x < 256

//@NativeInt128
//newtype ubyte14 = x : int | 0 <= x < 256

@DisableNonlinearArithmetic
@Options("--function-syntax:3")
module SimpleLinearModule {
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
function g(y:int, b:bool) : bool
{
  if b then f(y + 2) else f(2*y)
}

@Concurrent
method ConcurrentMethod()
  modifies {}
{
}

@IsolateAssertions
method Test(a: int, b: int, c: int)
  requires a < b && b < c
{
  assert a < c; 
  assert c > a;
}

@Print
@Priority(2)
@ResourceLimit("1000")
@TimeLimit(1000)
method VerifyThisOnly() {
  print "hello";
  assert true;
}

@TailRecursion
@Transparent
@TimeLimitMultiplier(2)
function Fib(n: nat, a: int, b: int): int {
  if n == 0 then b
  else Fib(n - 1, b, a + b)
}

@Verify
@Test
@TestInline
@TestInline(10)
@TestEntry
@VcsMaxCost(10)
@VcsMaxKeepGoingSplits(10)
@VcsMaxSplits(10)
@IsolateAssertions
method TestItAll() {
  expect true;
}

@Synthesize
@Axiom
method Synthesizing(x: int) returns (y: int)
  ensures x == y + 1

