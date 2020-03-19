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
  print "TriangleNumber(10) = ", TriangleNumber(10), "\n";
  var xs := Cons(100, Cons(40, Cons(60, Nil)));
  print "Sum(", xs, ") = ", Sum(xs), "\n";
}

function method {:tailrecursion} TriangleNumber(n: nat): nat {
  if n == 0 then // test if-then-else
    0
  else
    n + TriangleNumber(n - 1) // test left accumulator
}

datatype List = Nil | Cons(head: int, tail: List)

function method {:tailrecursion} Sum(xs: List): int {
  match xs // test match
  case Nil =>
    assert xs.Nil?; // test StmtExpr
    var zero := 0; // test let expr
    zero
  case Cons(x, rest) =>
    Sum(xs.tail) + xs.head // test right accumulator
}
