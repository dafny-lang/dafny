// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method {:tailrecursion} A(q: int) returns (x: int, ghost y: bool, z: nat)
{
  if (q < 10) {
    x, y, z := 15, true, 20;
  } else {
    ghost var u;
    x, u, z := A(q-1);
    y := !u;
  }
}

method {:tailrecursion} B(q: int) returns (x: int, ghost y: bool, z: nat)
{
  if (q < 10) {
    x, y, z := 15, true, 20;
  } else {
    ghost var u;
    x, u, z := B(q-1);  // error: not a tail call, because it is followed by an increment to x
    y, x := !u, x + 1;
  }
}

method C(q: int) returns (x: int)
  decreases *;
{
  x := C(q-1);
}

method D(q: int) returns (x: int)
{
  x := D(q-1);
  x := x + 1;
}

method {:tailrecursion} E0(q: int) returns (x: int)  // error: not allowed, because the method is not
  // tail recursive (since mutually recursive methods are currently not recognized as being tail recursive)
{
  x := E1(q-1);
}
method {:tailrecursion} E1(q: int) returns (x: int)  // error: not allowed, because the method is not
  // tail recursive (since mutually recursive methods are currently not recognized as being tail recursive)
{
  x := E0(q);
}

method F0(q: int) returns (x: int)
  decreases *;  // fine
{
  x := D(q);
}
method F1(q: int) returns (x: int)
  decreases 5;  // since this is okay (that is, you can--for no particular reason--add a 'decreases' clause to a non-recursive method), the 'decreases *' above is also allowed
{
  x := D(q);
}

method {:tailrecursion} G0(q: int) returns (x: int)
  decreases *;
{
  x := D(q);
}
method {:tailrecursion false} G1(q: int) returns (x: int)  // the annotation tells the compiler not to tail-call optimize
  decreases *;
{
  x := G1(q);
}

method H0(q: int) returns (x: int)
  decreases *;  // fine
method {:tailrecursion} H1(q: int) returns (x: int)
  decreases *;  // fine
method H2(q: int) returns (x: int)
  decreases 5;  // fine

class {:autocontracts} MyAutoContractClass {
  var left: MyAutoContractClass?

  predicate Valid() { true }

  method {:tailrecursion} VisitLeft(val: int)
  {
    if left != null {
      left.VisitLeft(val);  // this is a tail call, because what :autocontracts appends is ghost
    }
  }
}

method {:tailrecursion} OtherTailCall(n: int) {
  ghost var x := 12;
  if n > 0 {
    OtherTailCall(n-1);  // tail call
  }
  x := 14;
  { x := 13; }
  ghost var h := 15;
  if n < h*30 { } // this is a ghost statement as well
  if n < 230 { } // and this can be (and is) considered ghost as well
  if (*) { x := x + 1; }  // this, too
}

class TailConstructorRegressionTest
{
  var next: TailConstructorRegressionTest
  constructor {:tailrecursion} (n: nat)
  {
    if n != 0 {
      next := new TailConstructorRegressionTest(n-1);  // error: not a tail call, because it is followed by an assignment
    }
  }
}

class TailConstructorRegressionTest'
{
  method {:tailrecursion} Compute<G(0)>(n: nat)
  {
    if n == 0 {
      print "\n";
    } else if n % 2 == 1 {
      var g: G;
      print g, " ";
      Compute<G>(n-1);
    } else {
      Compute<bool>(n-1);  // error: not a tail call, because the type parameters don't match
    }
  }

  method {:tailrecursion} Run<H,G(0)>(n: nat)
  {
    if n == 0 {
      print "\n";
    } else if n % 2 == 1 {
      var g: G;
      print g, " ";
      Run<H,G>(n-1);
    } else {
      Run<H,bool>(n-1);  // error: not a tail call, because the type parameters don't match
    }
  }
}

// ------------ tail-recursive functions --------------------------

function method {:tailrecursion} R(n: nat): nat
  decreases n
{
  if n % 5 == 0 then
    10
  else if n % 5 == 1 then
    R(n - 1)
  else if n % 5 == 2 then
    R(n - 2)
  else if n % 5 == 3 then
    ghost var r := R(n - 2);  // fine, R is used in ghost expression
    assert R(n - 2) == 10;  // fine, R is used in ghost expression
    R(n - 2)
  else
    U(-2, R(n - 1))  // fine, R is used for ghost parameter
}

function method U(x: int, ghost y: int): nat
  requires x < y
{
  if x < 0 then -x else x
}

function method {:tailrecursion} Q(n: nat): nat {
  if n % 5 == 0 then
    var s := Q;  // error: this use of Q is not a tail call
    10
  else if n % 5 == 1 then
    Q(Q(n - 1))  // error: inner Q is not a tail call
  else if n % 5 == 2 then
    Q(n - 2) + 3  // error: Q is not a tail call
  else if n % 5 == 3 then
    var r := Q(n - 2);  // error: not a tail call
    Q(n - 2)
  else
    U(Q(n - 1), Q(n - 1) + 10)  // error: first Q has to be a tail call
}

function {:tailrecursion false} Gh0(n: nat): nat {  // fine
  15
}

function {:tailrecursion} Gh1(n: nat): nat {  // error: {:tailrecursion true} cannot be used with ghost functions
  15
}

ghost method {:tailrecursion false} Gh2(n: nat) {  // fine
}

ghost method {:tailrecursion} Gh3(n: nat) {  // error: {:tailrecursion true} cannot be used with ghost methods
}

// ----- auto-accumulator tail recursion -----

function method {:tailrecursion} TriangleNumber(n: nat): nat {
  if n == 0 then
    0
  else if n % 2 == 0 then
    TriangleNumber(n - 1) + n
  else
    n + TriangleNumber(n - 1)
}

newtype MyInt = int
function method {:tailrecursion} SumMyInt(n: MyInt): MyInt
  requires 0 <= n
{
  if n == 0 then 0 else n + SumMyInt(n - 1)
}

newtype MyConstrainedInt = x | x % 2 == 0
function method {:tailrecursion} SumMyConstrainedInt(n: nat): MyConstrainedInt { // error: constrained types cannot be auto-accumulator tail recursive
  if n == 0 then 0 else (2 * n) as MyConstrainedInt + SumMyConstrainedInt(n - 1)
}

type Even = x | x % 2 == 0
function method {:tailrecursion} SumEven(n: nat): Even { // error: constrained types cannot be auto-accumulator tail recursive
  if n == 0 then 0 else (2 * n) as Even + SumEven(n - 1)
}

function method {:tailrecursion} TriangleNumberSeq(n: nat): seq<nat> {
  if n == 0 then
    [0]
  else if n % 2 == 0 then // error: then/else use different accumulators
    TriangleNumberSeq(n - 1) + [n]
  else
    [n] + TriangleNumberSeq(n - 1)
}

datatype List = Nil | Cons(head: int, tail: List)

function method {:tailrecursion} Sum(xs: List, u: int): int {
  var uu := u + 1;
  if u % 2 == 0 then
    match xs {
      case Nil =>
        assert xs.Nil?; // test StmtExpr
        var zero := 0; // test let expr
        zero
      case Cons(x, rest) =>
        Sum(xs.tail, uu) + xs.head // right accumulator
    }
  else
    match xs {
      case Nil =>
        assert xs.Nil?;
        var zero := 0;
        zero
      case Cons(x, rest) =>
        xs.head + Sum(xs.tail, uu) // left accumulator
    }
}

function method {:tailrecursion} Tum(xs: List, u: int): seq<int> {
  var uu := u + 1;  // test let expr
  if u % 2 == 0 then // error: then/else use different accumulators
    match xs {
      case Nil =>
        assert xs.Nil?; // test StmtExpr
        var zero := 0; // test let expr
        [zero]
      case Cons(x, rest) =>
        Tum(xs.tail, uu) + [xs.head] // right accumulator
    }
  else
    match xs {
      case Nil =>
        assert xs.Nil?;
        var zero := 0;
        [zero]
      case Cons(x, rest) =>
        [xs.head] + Tum(xs.tail, uu) // left accumulator
    }
}

function method {:tailrecursion} Gum(xs: List): int {
  match xs
  case Nil =>
    assert xs.Nil?;
    var zero := 0;
    zero
  case Cons(x, rest) =>
    xs.head + Gum(xs.tail) + xs.head // error: this is not a simple accumulating tail call
}

function method {:tailrecursion} Hum(xs: List, b: bool): int {
  match xs
  case Nil =>
    if b then Hum(xs, false) else 0
  case Cons(x, rest) =>
    Hum(xs.tail, b) + xs.head
}

function method {:tailrecursion} Mum(xs: List, b: bool): int {
  match xs
  case Nil =>
    if b then 15 + Mum(xs, false) else 0
  case Cons(x, rest) =>
    Mum(xs.tail, b) + xs.head
}

function method {:tailrecursion} Bum(xs: List, b: bool): int {
  match xs
  case Nil =>
    if b then 15 - Bum(xs, false) else 0  // error: - only supports tail call on left (accumulator on right)
  case Cons(x, rest) =>
    Bum(xs.tail, b) - xs.head
}

function method {:tailrecursion} TailBv(n: bv5): bv5 {
  if n == 0 then 0 else TailBv(n - 1) + n  // error: because bitvector types are (currently) not supported in tail calls
}

function method {:tailrecursion} TailChar(n: int): char
  requires 0 <= n <= 20
  ensures TailChar(n) as int == 60 + n
{
  if n == 0 then 60 as char else TailChar(n - 1) + 1 as char  // error: because char is (currently) not supported in tail calls
}

// ------------ more methods --------------------------

method DoSomethingElse() {
}

method {:tailrecursion} MissingReport(n: nat, acc: nat) returns (r: nat)
  ensures r == n + acc
{
  ghost var g := 10;  // this initial ghost statement once caused the rest of the method body to be ignored
  if n == 0 {
    return acc;
  } else {
    r := MissingReport(n - 1, acc + 1);  // error: not a tail call
    DoSomethingElse();
  }
}

method {:tailrecursion} NoRecursiveCalls(n: nat, acc: nat) returns (r: nat)
  ensures r == n + acc
{
  ghost var g := 10;
  var u := 8;
  DoSomethingElse();
  u := u + 3;
  g := g + u;
}

method {:tailrecursion} GhostLoop(n: nat) returns (r: nat) {
  if n == 0 {
    return 0;
  } else {
    r := GhostLoop(n - 1);  // yes, this is a tail call
    while 15 < 14 {  // this is a ghost loop
    }
  }
}

method {:tailrecursion} NonGhostLoop(n: nat) returns (r: nat)
  decreases *
{
  if n == 0 {
    return 0;
  } else {
    r := NonGhostLoop(n - 1);  // error: not a tail call
    while 15 < 14  // because of the "decreases *", this is not a ghost loop
      decreases *
    {
    }
  }
}

function {:tailrecursion} FBM0(n: nat, x: int): int {
  x
} by method {
  return if n == 0 then x else FBM0(n - 1, x); // error: not recognized as tail recursive
}

function {:tailrecursion} FBM0'(n: nat, x: int): (r: int) {
  x
} by method {
  if n == 0 {
    return x;
  } else {
    r := FBM0'(n - 1, x);
  }
}

function {:tailrecursion} FBM0''(n: nat, x: int): (r: int) {
  x
} by method {
  if n == 0 {
    return x;
  } else {
    return FBM0''(n - 1, x);
  }
}

function {:tailrecursion} FBM0'3(n: nat, x: int): int {
  x
} by method {
  if n == 0 {
    return x;
  } else {
    return FBM0'3(n - 1, x);
  }
}

function {:tailrecursion} FBM1(n: nat, x: int): int {
  x
} by method {
  return if n == 0 then x else FBM1(n - 1, x) + FBM1(n - 1, x); // error: not tail recursive
}

function {:tailrecursion} FBM2(n: nat, x: int): int {
  x
} by method {
  if n == 0 {
    return x;
  } else {
    var y := FBM2(n - 1, x); // error: not tail recursive
    var z := FBM2(n - 1, y);
    return z;
  }
}

function {:tailrecursion} FBM3(n: nat, x: int): (r: int) {
  x
} by method {
  if n == 0 {
    return x;
  } else {
    var y := FBM3(n - 1, x); // error: not recognized as tail recursive
  }
}

function {:tailrecursion} FBM4(n: nat, x: int): (r: int) {
  x
} by method {
  if n == 0 {
    return x;
  } else {
    var y;
    if * {
      r, y := FBM4(n - 1, x), 450; // error: not recognized as tail recursive
    } else {
      y, r := 450, FBM4(n - 1, x); // error: not recognized as tail recursive
    }
  }
}

function {:tailrecursion} FBM5(n: nat, x: int): (r: int) {
  x
} by method {
  r := x;
  if n != 0 {
    var arr := new real[100];
    arr[if FBM5(n - 1, x) % 2 == 0 then 3 else 4] := 98.6; // error: not recognized as tail recursive
  }
}
