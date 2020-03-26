// RUN: %dafny /compile:3 /compileTarget:cs "%s" > "%t"
// RUN: %dafny /compile:3 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /compile:3 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /compile:3 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  // In the following, 2_000_000 is too large an argument without tail-calls
  var x := M(2_000_000, 0);
  var y := F(2_000_000, 0);
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
}

method {:tailrecursion} M(n: nat, a: nat) returns (r: nat) {
  if n == 0 {
    return a;
  } else {
    // do a test that would fail if the actual parameters are not first
    // computed into temporaries, before they are assigned to the formals
    var p := n + a;
    r := M(n - 1 + n+a-p, a + 1 + n+a-p);
  }
}

function method {:tailrecursion} F(n: nat, a: nat): nat {
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
  print "Union(8) = ", Union(8), "\n";
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
