// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function Fib(n: int): int
  requires 0 <= n;
  ensures 0 <= Fib(n);
{
  if n < 2 then n else
  Fib(n-2) + Fib(n-1)
}

datatype List = Nil | Cons(int, List)

function Sum(a: List): int
  ensures 0 <= Sum(a);
{
  match a
  case Nil => 0
  case Cons(x, tail) => if x < 0 then 0 else Fib(x)
}

function FibWithoutPost(n: int): int
  requires 0 <= n;
{
  if n < 2 then n else
  FibWithoutPost(n-2) + FibWithoutPost(n-1)
}

function SumBad(a: List): int
  ensures 0 <= Sum(a);  // this is still okay, because this is calling the good Sum
  ensures 0 <= SumBad(a);  // error: cannot prove postcondition
{
  match a
  case Nil => 0
  case Cons(x, tail) => if x < 0 then 0 else FibWithoutPost(x)
}

function FibWithExtraPost(n: int): int
  ensures 2 <= n ==> 0 <= FibWithExtraPost(n-1); // This is fine, because the definition of the function is discovered via canCall
  ensures 1 <= n ==> 0 <= FibWithExtraPost(n-1); // Error: In the current implementation of Dafny, one needs to actually call the
                                                 // function in order to benefit from canCall.  This may be improved in the future.
  ensures 0 <= FibWithExtraPost(n);
{
  if n < 0 then 0 else
  if n < 2 then n else
  FibWithExtraPost(n-2) + FibWithExtraPost(n-1)
}

function DivergentPost(n: int): int
  requires 0 <= n;
  ensures 1 <= n ==> DivergentPost(n-1) == DivergentPost(n-1);
  ensures DivergentPost(2*n - n) == DivergentPost(2*(n+5) - 10 - n);  // these are legal ways to denote the result value of the function
  ensures DivergentPost(n+1) == DivergentPost(n+1);  // error: call may not terminate
{
  assert 2*n - n == 2*(n+5) - 10 - n;
  if n < 2 then n else
  DivergentPost(n-2) + DivergentPost(n-1)
}

function HoldsAtLeastForZero(x: int): bool
  ensures x == 0 ==> HoldsAtLeastForZero(x);
{
  x < -2  // error: this does not hold for 0
}

// ----- Some functions that deal with let-such-that and if-then-else expressions and having them pass
// ----- the subrange test (which they didn't always do).

function IncA(x: nat): nat
  ensures x < IncA(x);
{
  if x == 17 then
    18
  else
    var y :| x < y;
    y
}

ghost method M() {
  var z := IncA(10);
  assert z != 0;
}

function IncB(i: nat): nat
{
  var n :| n>i; n
}

function IncC(i: nat): int
  ensures IncC(i)>=0;
{
  var n :| n>i; n
}


/////////////////////////////////////////////////////////////
//  Test :opaque functions
/////////////////////////////////////////////////////////////

// Test basic function hiding
function {:opaque} secret(x:int, y:int) : int
  requires 0 <= x < 5;
  requires 0 <= y < 5;
  ensures secret(x, y) < 10;
{ x + y }

method test_secret()
{
  assert secret(2, 3) >= 5;   // Should fail because secret's body is hidden
  reveal secret();
  assert secret(2, 3) == 5;   // Should pass now that the body is "visible"
  assert secret(4, 1) == 7;   // Make sure it catches incorrect applications as well
}

// Check that opaque doesn't break recursion unrolling
// Also checks that opaque functions that do terminate are verified as such
function {:opaque} recursive_f(x:int) : int
  requires x >= 0;
{
  if x == 0 then 0
  else 1 + recursive_f(x - 1)
}

method test_recursive_f()
{
  if * {
    assert recursive_f(4) == 4;   // Should fail because body is hidden
  } else {
    reveal recursive_f();
    assert recursive_f(4) == 4;   // Should pass now body is visible and can be unrolled
    assert recursive_f(3) == 5;   // Make sure it catches incorrect applications as well
  }
}

// Check that opaque doesn't interfere with ensures checking
function {:opaque} bad_ensures(x:int, y:int):int
  requires x >= 0 && y >= 0;
  ensures bad_ensures(x, y) > 0;
{
  x + y
}

// Check that opaque doesn't interfere with termination checking
function {:opaque} f(i:int):int
  decreases i;
{
  f(i) + 1
}

// Try a sneakier (nested) version of the test above
function {:opaque} g(i:int):int
  decreases i;
{
  h(i) + 1
}

function h(i:int):int
{
  g(i)
}
