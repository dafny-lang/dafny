// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint.dfy" "%s" > "%t"
// RUN: %dafny /noVerify /compile:0 "%t.dprint.dfy" >> "%t"
// RUN: %diff "%s.expect" "%t"

method M0(n: int)
  requires var f := 100; n < f; requires var t, f := true, false; (t && f) || n < 100;
{
  assert n < 200;
  assert 0 <= n;  // error
}

method M1()
{
  assert var f := 54; var g := f + 1; g == 55;
}

method M2()
{
  assert var f := 54; var f := f + 1; f == 55;
}

function Fib(n: nat): nat
{
  if n < 2 then n else Fib(n-1) + Fib(n-2)
}

method M3(a: array<int>) returns (r: int)
  requires forall i :: 0 <= i < a.Length ==> a[i] == 6;
  ensures (r + var t := r; t*2) == 3*r;
{
  assert Fib(2) + Fib(4) == Fib(0) + Fib(1) + Fib(2) + Fib(3);

  {
    var x,y := Fib(8), Fib(11);
    assume x == 21;
    assert Fib(7) == 3 ==> Fib(9) == 24;
    assume Fib(1000) == 1000;
    assume Fib(9) - Fib(8) == 13;
    assert Fib(9) <= Fib(10);
    assert y == 89;
  }

  assert Fib(1000) == 1000;  // does it still know this?

  forall i | 0 <= i < a.Length ensures true; {
    var j := i+1;
    assert j < a.Length ==> a[i] == a[j];
  }
}

// M4 is pretty much the same as M3, except with things rolled into expressions.
method M4(a: array<int>) returns (r: int)
  requires forall i :: 0 <= i < a.Length ==> a[i] == 6;
  ensures (r + var t := r; t*2) == 3*r;
{
  assert Fib(2) + Fib(4) == Fib(0) + Fib(1) + Fib(2) + Fib(3);
  assert
    var x,y := Fib(8), Fib(11);
    assume x == 21;
    assert Fib(7) == 3 ==> Fib(9) == 24;
    assume Fib(1000) == 1000;
    assume Fib(9) - Fib(8) == 13;
    assert Fib(9) <= Fib(10);
    y == 89;
  assert Fib(1000) == 1000;  // still known, because the assume was on the path here
  assert forall i :: 0 <= i < a.Length ==> var j := i+1; j < a.Length ==> a[i] == a[j];
}

class AClass {
  var index: int;
  method P(a: array<int>) returns (b: bool, ii: int)
    requires exists k :: 0 <= k < a.Length && a[k] == 19;
    modifies this, a;
    ensures ii == index;
    // The following uses a variable with a non-old definition inside an old expression:
    ensures 0 <= index < a.Length && old(a[ii]) == 19;
    ensures 0 <= index < a.Length && var newIndex := index; old(a[newIndex]) == 19;
    // The following places both the variable and the body inside an old:
    ensures b ==> old(var oldIndex := index; 0 <= oldIndex < a.Length && a[oldIndex] == 17);
    // Here, the definition of the variable is old, and it's used both inside and
    // inside an old expression:
    ensures var oi := old(index); oi == index ==> a[oi] == 21 && old(a[oi]) == 19;
  {
    b := 0 <= index < a.Length && a[index] == 17;
    var i, j := 0, -1;
    while (i < a.Length)
      invariant 0 <= i <= a.Length;
      invariant forall k :: 0 <= k < i ==> a[k] == 21;
      invariant forall k :: i <= k < a.Length ==> a[k] == old(a[k]);
      invariant (0 <= j < i && old(a[j]) == 19) ||
                (j == -1 && exists k :: i <= k < a.Length && a[k] == 19);
    {
      if (a[i] == 19) { j := i; }
      i, a[i] := i + 1, 21;
    }
    index := j;
    ii := index;
  }

  method PMain(a: array<int>)
    requires exists k :: 0 <= k < a.Length && a[k] == 19;
    modifies this, a;
  {
    var s := a[..];
    var b17, ii := P(a);
    assert s == old(a[..]);
    assert s[index] == 19;
    if (*) {
      assert a[index] == 19;  // error (a can have changed in P)
    } else {
      assert b17 ==> 0 <= old(index) < a.Length && old(a[index]) == 17;
      assert index == old(index) ==> a[index] == 21 && old(a[index]) == 19;
    }
  }
}

// ---------- lemmas ----------

method Theorem0(n: int)
  requires 1 <= n;
  ensures 1 <= Fib(n);
{
  if (n < 3) {
  } else {
    Theorem0(n-2);
    Theorem0(n-1);
  }
}

ghost method Theorem1(n: int)
  requires 1 <= n;
  ensures 1 <= Fib(n);
{
  // in a ghost method, the induction tactic takes care of it
}

ghost function Theorem2(n: int): int
  requires 1 <= n;
  ensures 1 <= Fib(n);
{
  if n < 3 then 5 else
    var x := Theorem2(n-2);
    var y := Theorem2(n-1);
    x + y
}

ghost function Theorem3(n: int): int
  requires 1 <= n;
  ensures 1 <= Fib(n);
{
  if n < 3 then 5 else
    var x := Theorem3(n-2);
    var y := Theorem3(n-1);
    5
}

// ----- tricky substitution issues in the implementation -----

class TrickySubstitution {
  ghost function F0(x: int): int
    ensures F0(x) == x;
  {
    var g :| x == g;
    g
  }

  ghost function F1(x: int): int
    ensures F1(x) == x;
  {
    var f := x;
    var g :| f == g;
    g
  }

  ghost function F2(x: int): int
    ensures F2(x) == x;
  {
    var f, g :| f == x && f == g;
    g
  }

  ghost function F3(x: int): int
    ensures F3(x) == x;
  {
    var f :| f == x;
    var g :| f == g;
    g
  }

  var v: int;
  var w: int;

  ghost function F4(x: int): int
    requires this.v + x == 3 && this.w == 2;
    reads this;
    ensures F4(x) == 5;
  {
    var f := this.v + x;  // 3
    var g :| f + this.w == g;  // 5
    g
  }

  // let-such-thats inside quantifiers must have quantified vars substituted correctly
  ghost predicate F5(n: int)
  {
    forall i :: 0 < i < n ==> var j, k :| k <= j < i; k <= j < i
  }

  method M(x: int)
    requires this.v + x == 3 && this.w == 2;
    modifies this;
  {
    this.v := this.v + 1;
    this.w := this.w + 10;
    assert 6 ==
      var f := this.v + x;  // 4
      var g :| old(f + this.w) == g;  // 6
      g;
  }

  method N() returns (ghost r: int, ghost s: int)
    requires w == 12;
    modifies this;
    ensures r == 12 == s && w == 13;
  {
    w := w + 1;
    r := var y :| y == old(w); y;
    s := old(var y :| y == w; y);
  }
}

datatype List<T> = Nil | Cons(head: T, tail: List)

method Q(list: List<int>, anotherList: List<int>)
  requires list != Nil;
{
  var x :=
    var Cons(h, t) := list;
    Cons(h, t);
  var y := match anotherList
    case Nil => (match anotherList case Nil => 5)
    case Cons(h, t) => h;
  assert list == x;
  assert anotherList.Cons? ==> y == anotherList.head;
  assert anotherList.Nil? ==> y == 5;
}

// ------------- pattern LHSs ---------------

datatype Tuple<T,U> = Pair(0: T, 1: U)

function Together(x: int, y: bool): Tuple<int, bool>
{
  Pair(x, y)
}

method LikeTogether() returns (z: int)
{
  if * {
    z := var Pair(xx: nat, yy) := Together(-10, true); xx + 3;  // error: int-to-nat failure
    assert 0 <= z;  // follows from the bogus type of xx
  } else if * {
    var t: nat := -30;  // error: int-to-nat failure in assignment statement
  } else {
    z := var t: nat := -30; t;  // error: int-to-nat failure in let expression
  }
}

method Mountain() returns (z: int, t: nat)
{
  z := var Pair(xx: nat, yy) := Together(10, true); xx + 3;
  assert 0 <= z;
}

function Rainbow<X>(tup: Tuple<X, int>): int
  ensures 0 <= Rainbow(tup);
{
  var Pair(left, right) := tup; right*right
}

datatype Friend = Agnes(int) | Agatha(int) | Jermaine(int) | Jack(int)

ghost function Fr(x: int): Friend
{
  if x < 10 then Jermaine(x) else Agnes(x)
}

method Friendly(n: nat) returns (ghost c: int)
  ensures c == n;
{
  if n < 3 {
    c := var Jermaine(y) := Fr(n); y;
  } else {
    c := var Agnes(y) := Fr(n); y;  // error: Fr might return something other than an Agnes
  }
}

function F_good(d: Tuple<
                             Tuple<bool, int>,
                             Tuple< Tuple<int,int>, Tuple<bool,bool> >>): int
  requires 0 <= d.1.0.1 < 100;
{
  var p, Pair(Pair(b0, x), Pair(Pair(y0, y1: nat), Pair(b1, b2))), q: int := d.0, d, d.1.0.1;
  assert q < 200;
  p.1 + if b0 then x + y0 else x + y1
}
function F_bad(d: Tuple<
                            Tuple<bool, int>,
                            Tuple< Tuple<int,int>, Tuple<bool,bool> >>): int
{
  var p, Pair(Pair(b0, x), Pair(Pair(y0, y1: nat), Pair(b1, b2))), q: int  // error: int-to-nat failure
   := d.0, d, d.1.0.1;
  assert q < 200;  // error: assertion failure
  p.1 + if b0 then x + y0 else x + y1
}

// ----------------------------------

method LetSuchThat_Deterministic() returns (x: int)
{
  if {
    case true =>
      x := var y :| y < 0; y;  // error: not deterministic
    case true =>
      x := var y :| y < 0; y*0;
    case true =>
      x := var w :| w == 2*w; w;
  }
  var t := {3, 5};
  var s := var a, b :| a in t && b in t && a != b; {a} + {b};
  assert s == t;
}

// ----------------------------------

module PatternsWithExplicitTypes {
  datatype Tuple<T,U> = Pair(0: T, 1: U)
  method LetExpr(p: Tuple<nat,bool>, q: Tuple<int,bool>) returns (z: int)
  {
    z := var Pair(xx: nat, yy) := q; xx;  // error: int-to-nat failure
  }
  method LetStmt(p: Tuple<nat,bool>, q: Tuple<int,bool>) returns (z: int)
  {
    var Pair(xx: nat, yy) := q;  // error: int-to-nat failure
  }
  method LetExpr'(p: Tuple<nat,bool>, q: Tuple<int,bool>) returns (z: int)
  {
    z := var Pair(xx: int, yy) := p; xx;
  }
  method LetStmt'(p: Tuple<nat,bool>, q: Tuple<int,bool>) returns (z: int)
  {
    var Pair(xx: int, yy) := p;
  }
}

// ----------------------------------

module CanCallRegressionTests {
  class C {
    var x: int

    function Id(c: C): C { c }

    method M()
    {
      assert Id(this) == this;
      var e := Id(this).x;
      assert (var c: C :| c == this; c) == this;
      var d := (var c: C :| c == this; c).x;  // this once used to fail with a non-deref error, because of a missing CanCall assumption
    }
  }
}

// ---------------------------------- Lit of let RHS

module LitLet {
  function Gauss(n: nat): nat {
    if n == 0 then 0 else n + Gauss(n - 1)
  }

  method M0() {
    assert Gauss(12) == 78;
  }
  method M1() {
    assert Gauss(20 - 8) == 78;
  }
  method M2() {
    var twenty := 20;
    var eight := 8;
    assert Gauss(twenty - eight) == 78;  // error: Lit doesn't get this case
  }
  method M3() {
    var twelve :=
      var twenty := 20;
      var eight := 8;
      twenty - eight;
    assert Gauss(twelve) == 78;
  }

  method P(a: nat, b: nat)
    requires a == 20 && b == 8
  {
    assert Gauss(a - b) == 78;  // error: Lit doesn't get this case
  }

  // ---

  datatype Nat = O | S(pred: Nat)

  ghost function plus(n: Nat, m: Nat) : Nat {
    match n
    case O => m
    case S(n') => S(plus(n', m))
  }

  ghost function mult(n: Nat, m: Nat) : Nat {
    if n.O? then O else
      var n' := n.pred;
      plus(m, mult(n', m))
  }

  ghost function factorial(n: Nat): Nat {
    match n
    case O => S(O)
    case S(n') => mult(n, factorial(n'))
  }

  lemma Test() {
    var n2 := S(S(O));
    var n3 := S(n2);
    var n5 := S(S(n3));
    var n10 := plus(n5, n5);
    var n12 := S(S(n10));

    assert factorial(n5) == mult(n10, n12);
  }
}
