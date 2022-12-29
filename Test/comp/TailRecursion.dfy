// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=java "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=js "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=go "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=py "%s" "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  // In the following, 2_000_000 is too large an argument without tail-calls
  var x := M(2_000_000, 0);
  var y := F(2_000_000, 0);
  print x, " ", y, "\n";  // 2_000_000 2_000_000

  x := TestMethod(2_000_000, 0);  // too large argument without tail-calls
  y := GhostAfterCall(2_000_000, 0);  // too large argument without tail-calls
  print x, " ", y, "\n";  // 2_000_000 2_000_000

  // create a cycle of 2 links
  var l0 := new Link(0);
  var l1 := new Link(1);
  l0.next, l1.next := l1, l0;

  x := l0.G(2_000_000, 0);  // too large argument without tail-calls
  y := l0.H(2_000_000, 0);  // too large argument without tail-calls
  print x, " ", y, "\n";  // 1_000_000 1_000_000

  var total := PrintSum(10, 0, "");
  print " == ", total, "\n";

  AutoAccumulatorTests();

  Regression.Test();

  // In the following, 2_000_000 is too large an argument without tail-calls
  x := FunctionByMethodTailRecursion(2_000_000);
  print x, "\n";  // 2_000_000
}

method {:tailrecursion} M(n: nat, a: nat) returns (r: nat) {
  if n == 0 {
    r := a;
  } else {
    // do a test that would fail if the actual parameters are not first
    // computed into temporaries, before they are assigned to the formals
    var p := n + a;
    r := M(n - 1 + n+a-p, a + 1 + n+a-p);
  }
}

method {:tailrecursion} TestMethod(n: nat, acc: nat) returns (r: nat) {
  if n == 0 {
    r := acc + 1;
    return r - 1;
  } else {
    r := TestMethod(n - 1, acc + 1);
  }
}

method {:tailrecursion} GhostAfterCall(n: nat, acc: nat) returns (r: nat) {
  ghost var g := 10;
  if n == 0 {
    // make sure ghost compilation doesn't produce malformed code
    var u := 20;
    if acc == 300 {
      u := u + 1;
    } else {
      // empty (thus ghost) else
    }
    if acc == 300 {
    } else if g < 25 {  // ghost if
    }
    if acc == 300 {
      u := u + 1;
    }  // this has an omitted else

    return acc;
  } else {
    r := GhostAfterCall(n - 1, acc + 1);
    // all of what follows is ghost; this tests that nothing is emitted
    // (Java would complain if any code were omitted after a "continue;")
    ghost var gg := 10;
    { }
    { g := g + 1; }
    { ghost var h := 8; g := g + 1; }
    {
      // if with ghost guards
      if g % 2 == 0 {
        // empty
      } else if g % 3 == 0 {
        g := g + 1;  // ghost assignment
      }  // else omitted
    }
    {
      // if with compilable guards
      if n % 2 == 0 {
        // empty
      } else if n % 3 == 0 {
        g := g + 1;  // ghost assignment
      }  // else omitted
    }
    {
      { }  // nested block
      g := g + 1;
      { ghost var i: int; }
      { if n % 5 == 0 { } else { } }  // explicit else block
    }
    if n == 0 {
      label LabeledBlock: { }
    }
    if n == 1 {
      label LabeledStatement: assert true;
    }
    while 15 < 14 {  // this compiles to nothing, since the whole statement is ghost
    }
  }
}

function method {:tailrecursion} F(n: nat, a: nat): nat {
  ghost var irrelevantGhost := 10;
  if n == 0 then
    a
  else
    // do a test that would fail if the actual parameters are not first
    // computed into temporaries, before they are assigned to the formals
    var p := n + a;
    F(n - 1 + n+a-p, a + 1 + n+a-p)
}

class Link {
  var x: nat
  var next: Link
  constructor (y: nat) {
    x := y;
    next := this;
  }

  method G(n: nat, a: nat) returns (r: nat)  {
    if n == 0 {
      return a;
    } else {
      r := next.G(n - 1, a + x);
    }
  }

  function method {:tailrecursion} H(n: nat, a: nat): nat
    reads *
  {
    if n == 0 then a else next.H(n - 1, a + x)
  }
}

method PrintSum(n: nat, acc: nat, prefix: string) returns (total: nat) {
  if n == 0 {
    total := acc;  // test that this fall-through is handled correctly
  } else {
    print prefix, n;
    total := PrintSum(n - 1, n + acc, " + "); // tail recursion
  }
}

// ----- auto-accumulator tail recursion -----

method AutoAccumulatorTests() {
  print "TriangleNumber(10) = ", TriangleNumber(10), "\n"; // 55
  print "TriangleNumber_Real(10) = ", TriangleNumber_Real(10), "\n"; // 55.0
  print "TriangleNumber_ORDINAL(10) = ", TriangleNumber_ORDINAL(10), "\n"; // 55
  print "Factorial(5) = ", Factorial(5), "\n";
  var u := SetToSeq(Union(8));
  print "Union(8) = ", u, "\n";
  print "UpTo(10) = ", UpTo(10), "\n";
  print "DownFrom(10) = ", DownFrom(10), "\n";
  var xs := Cons(100, Cons(40, Cons(60, Nil)));
  print "Sum(", xs, ") = ", Sum(xs), "\n";
  print "TheBigSubtract(100) = ", TheBigSubtract(100), "\n"; // -12
  print "TailNat(10) = ", TailNat(10), "\n";
}

function method {:tailrecursion} TriangleNumber(n: nat): nat {
  if n == 0 then // test if-then-else
    0
  else if n % 2 == 0 then
    TriangleNumber(n - 1) + n // test right accumulator
  else
    n + TriangleNumber(n - 1) // test left accumulator
}

function method {:tailrecursion} TriangleNumber_Real(n: nat): real {
  if n == 0 then // test if-then-else
    0.0
  else
    TriangleNumber_Real(n - 1) + n as real
}

function method {:tailrecursion} TriangleNumber_ORDINAL(n: nat): ORDINAL {
  if n == 0 then // test if-then-else
    0
  else
    TriangleNumber_ORDINAL(n - 1) + n as ORDINAL
}

function method {:tailrecursion} Factorial(n: nat): nat {
  if n == 0 then // test if-then-else
    1
  else if n % 2 == 0 then
    Factorial(n - 1) * n // test right accumulator
  else
    n * Factorial(n - 1) // test left accumulator
}

function method {:tailrecursion} Union(n: nat): set<nat> {
  if n == 0 then // test if-then-else
    {0}
  else if n % 2 == 0 then
    Union(n - 1) + {n} // test right accumulator
  else
    {n} + Union(n - 1) // test left accumulator
}

method SetToSeq(S: set<nat>) returns (r: seq<nat>) {
  if S == {} {
    return [];
  }
  var x :| x in S;
  var smaller := set y | y in S && y < x;
  var larger := set y | y in S && x < y;
  var s := SetToSeq(smaller);
  var l := SetToSeq(larger);
  return s + [x] + l;
}

method SetToSeq_Regression(S: set<nat>) returns (r: seq<nat>, g: int) {
  // Method "SetToSeq" once had a problem, which showed up in the compilation
  // to Java. This version of the method triggered the corresponding compilation
  // in C#.
  if S == {} {
    r := [];
    return;
  }
  var x :| x in S;
  g := x;
  var smaller := set y | y in S && y < g;
  var larger := set y | y in S && g < y;
  var s, _ := SetToSeq_Regression(smaller);
  var l, _ := SetToSeq_Regression(larger);
  r := s + [x] + l;
}

function method {:tailrecursion} UpTo(n: nat): seq<nat> {
  if n == 0 then
    ZeroSeq() // test non-recursive call
  else
    UpTo(n - 1) + [n] // test right-accumulator concat
}

function method {:tailrecursion} DownFrom(n: nat): seq<nat> {
  if n == 0 then
    ZeroSeq() // test non-recursive call
  else
    [n] + DownFrom(n - 1) // test left-accumulator concat
}

function method ZeroSeq(): seq<int> {
  [0]
}

datatype List = Nil | Cons(head: int, tail: List)

function method {:tailrecursion} Sum(xs: List): int {
  match xs // test match
  case Nil =>
    assert xs.Nil?; // test StmtExpr
    var zero := 0; // test let expr
    zero
  case Cons(x, rest) =>
    Sum(xs.tail) + xs.head
}

function method {:tailrecursion} TheBigSubtract(n: nat): int
  ensures TheBigSubtract(n) == 88 - n
{
  if n == 0 then
    88
  else
    TheBigSubtract(n - 1) - 1 // test subtraction accumulation
}

function method {:tailrecursion} TailNat(n: int): nat
  requires 0 <= n <= 20
  ensures TailNat(n) == 100 - 5 * n
{
  if n == 0 then 100 else
    // In this case, the accumulator's value will not be a "nat", but that's okay in the end
    (-5) + TailNat(n - 1)
}

// This module contains some regression tests for capture of "_this" and related crashes.
module Regression {
  method Test() {
    var i := 0;
    var c := new C<real>(null);
    while i < 100 {
      c := new C<real>(c);
      i := i + 1;
    }
    var x := c.Rec(100, () => -2);  // this should return 17
    var y := c.RecM(100, () => -2);  // this should return 17
    var z := c.RecM'(100, () => -2);  // this should return 17
    print x, " ", y, " ", z, "\n";
  }

  class C<U> {
    const data: int
    const next: C?<U>
    constructor (nx: C?<U>) {
      data := if nx == null then 10 else 1 + nx.data;
      next := nx;
    }

    function method F(): int {
      data
    }

    function method {:tailrecursion} Rec(n: nat, f: () -> int): int {
      if n == 0 || next == null then
        f()
      else if data == 17 then
        next.Rec(n - 1, F)  // this F returns 17
      else
        next.Rec(n - 1, f)
    }

    method {:tailrecursion} RecM(n: nat, f: () -> int) returns (r: int) {
      if n == 0 || next == null {
        r := f();
      } else if data == 17 {
        r := next.RecM(n - 1, F);  // this F returns 17
      } else {
        r := next.RecM(n - 1, f);
      }
    }

    method {:tailrecursion} RecM'(n: nat, f: () -> int) returns (r: int) {
      var th := null;
      if n == 0 || next == null {
        r := f();
      } else if data == 17 {
        th := this;
        r := next.RecM'(n - 1, th.F);  // this F returns 17
      } else {
        r := next.RecM'(n - 1, f);
      }
    }
  }
}

function FunctionByMethodTailRecursion(x: int, y: int := 0): (r: int) {
  x + y
} by method {
  if x < 8 || x == 77 {
    return x + y;
  } else {
    r := FunctionByMethodTailRecursion(x - 1, y + 1);
  }
}
