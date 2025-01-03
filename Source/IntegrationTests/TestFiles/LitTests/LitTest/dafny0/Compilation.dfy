// RUN: %testDafnyForEachCompiler "%s"


// The tests in this file are designed to run through the compiler.  They contain
// program snippets that are tricky to compile or whose compilation once was buggy.

module OnceBuggy {
  datatype MyDt<T> = Nil | Cons(T, MyDt<T>)

  method M<U>(x: MyDt<int>)
  {
    match (x) {
      case Cons(head, tail) =>
        var y: int := head;
      case Nil =>
    }
  }
}

// --------------------------------------------------

module CoRecursion {
  codatatype Stream<T> = More(head: T, rest: Stream)

  function AscendingChain(n: int): Stream<int>
  {
    More(n, AscendingChain(n+1))
  }

  datatype List<T> = Nil | Cons(car: T, cdr: List)

  function Prefix(n: nat, s: Stream): List
  {
    if n == 0 then Nil else
    Cons(s.head, Prefix(n-1, s.rest))
  }

  class Cell { var data: int }

  // When run, the following method should print
  //   400
  //   320
  //   40
  //   41
  //   42
  //   9
  //   9
  method TestMain() {
    var m := 17;
    var cell := new Cell;
    cell.data := 40;
    var mr := More(400, More(320, AscendingChain(cell.data)));
    m := 30;
    cell.data := 60;
    var l := Prefix(5, mr);
    while (l != Nil)
      decreases l
    {
      match (l) { case Cons(x,y) => }
      print l.car, "\n";
      l := l.cdr;
    }
    var nio := OneLess(0, 10);
    print nio, "\n";
    nio := OneLess'(0, 10);
    print nio, "\n";
  }

  method OneLess(lo: int, hi: int) returns (m: int)
    requires lo < hi
    // This method ensures m == hi - 1, but we don't care to prove it
    decreases hi - lo
  {
    if y {:nowarn} :| lo < y < hi {
      m := OneLess(y, hi);
    } else {
      m := lo;
    }
  }

  method OneLess'(lo: int, hi: int) returns (m: int)
    requires lo < hi
    // This method ensures m == hi - 1, but we don't care to prove it
    decreases hi - lo
  {
    if {
      case y {:nowarn} :| lo < y < hi =>
        m := OneLess'(y, hi);
      case lo+1 < hi =>
        m := OneLess'(lo+1, hi);
      case lo + 1 == hi =>
        m := lo;
    }
  }
}

abstract module S {
  class C {
    var f: int
    method m()
  }
}

module T refines S {
  class C ... {
    constructor () { }
    method m() {
      print "in T.C.m()";
    }
  }
}
module A {
   import X = T
   import Y = T
   import Z = T
   method run() {
     var x := new X.C();
     x.m();
     var y := new Y.C();
     y.m();
     var z := new Z.C();
     z.m();
   }
}

method NotMain() {
  A.run();
}


abstract module S1 {
  import B : T
  method do()
}

module T1 refines S1 {
  method do() {
    var x := 3;
  }
}
abstract module A1 {
   import X : T1
   method run() {
     X.do();
     var x := new X.B.C();
     x.m();
   }
}

// ----- keyword escapes (once buggy) -----

module M {
  datatype fixed = A | B
  function F(): fixed
  {
    A
  }
  class public {
    constructor() { }
    var private: int const namespace: int const fallthrough: int const try: int
  }
}

method Caller() {
  var p := new M.public();
  var x := p.private + p.namespace + p.fallthrough + p.try;
}

// ----- digits-identifiers for destructors -----

datatype Tuple<T,U> = Pair(0: T, 1: U, r: int, s': int)

method DigitsIdents(t: Tuple<int, Tuple<int, bool>>)
{
  var x: int := t.0;
  var y: bool := t.1.1;
  var z: int := t.r + t.1.r + t.1.s';
}

class DigitsClass {
  var 7: bool
  method M(c: DigitsClass)
  {
    var x: int := if this.7 then 7 else if c.7 then 8 else 9;
  }
}

// Should not get errors about methods or functions with empty bodies
// if they're marked with an :axiom attribute
ghost method {:axiom} m_nobody() returns (y:int)
  ensures y > 5

lemma {:axiom} l_nobody() returns (y:int)
  ensures y > 5

ghost function {:axiom} f_nobody():int
  ensures f_nobody() > 5

// Make sure the lemma created for opaque functions doesn't produce compiler errors
ghost function {:opaque} hidden():int
{
  7
}

method hidden_test()
{
  reveal hidden();
  assert hidden() == 7;
}

// ----- LetExpr with ghosts and in ghost contexts -----

module GhostLetExpr {
  method M() {
    ghost var y := *;
    var x := *;
    var g := G(x, y);
    ghost var h := var ta := F(); 5;
    var j := ghost var tb := F(); 5;
    assert h == j;
  }

  ghost function F(): int
  { 5 }

  function G(x: int, ghost y: int): int
  { assert y == y; x }

  datatype Dt = MyRecord(a: int, ghost b: int)

  method P(dt: Dt) {
    match dt {
      case MyRecord(aa, bb) =>
        ghost var z := bb + F();
        ghost var t0 := var y := z; z + 3;
        ghost var t1 := ghost var y := z; z + 3;
        var t2; t2 := ghost var y := z; aa + 3;
    }
  }

  function FM(): int
  {
    ghost var xyz := F();
    G(5, xyz)
  }
}

class DigitUnderscore_Names {
  // the following would be the same integers, but they are different fields
  var 0_1_0: int
  var 010: int
  var 10: int
  // ... as we see here:
  method M()
    modifies this
  {
    this.0_1_0 := 007;
    this.010 := 000_008;
    this.10 := 0x0000_0009;
    assert this.0_1_0 == 00_07.0_0 as int && this.010 == 8 && this.10 == 9;
    this.10 := 20;
  }
}

// ------------------------------------------------------------------

method Main()
{
  CoRecursion.TestMain();
  EqualityTests.TestMain();
  TypeInstantiations.TestMain();
  TailRecursionWhereTypeParametersChange.TestMain();
  GeneralMaps.Test();
  Cardinalities.Test();
  AltLoop.Test();
}

// ------------------------------------------------------------------

module EqualityTests {
  class C<T> {
  }

  method TestMain()
  {
    // regression tests:
    var a: C?<int>, b: C?<int> := null, null;
    if a == null {
      print "a is null\n";
    }
    if a != null {
      print "a is not null\n";
    }
    if a == b {
      print "a and b are equal\n";
    }
    if a != b {
      print "a and b are not equal\n";
    }

    var H := new real[10];
    ArrayTests(H);
  }

  method ArrayTests<T>(H: array?<T>)
  {
    var G := new int[10];
    if G as object == H {  // this comparison is allowed in Dafny, but requires a cast in C#
      print "this would be highly suspicious\n";
    }
    if G == H as object? {  // this comparison is allowed in Dafny, but requires a cast in C#
      print "this would be highly suspicious\n";
    }
    if G as object? != H {  // this comparison is allowed in Dafny, but requires a cast in C#
      print "? good world order\n";
    }
    if G != H as object? {  // this comparison is allowed in Dafny, but requires a cast in C#
      print "good world order ?\n";
    }
    if null == H {
      print "given array is null\n";
    }
    if null != H {
      print "given array is non-null\n";
    }
  }
}

// -------------------------------------------------
// Once buggy

method N()
{
  var z: nat :| true;
  assert 0 <= z;
}

// -------------------------------------------------

class DigitUnderscore_Names_Functions_and_Methods {
  ghost function 70(): int { 80 }
  lemma 120()
    ensures this.70() == 80
  {
  }

  const 90 := () => 92
  method 567(y: int) {
    var m := this.90;
    var k := this.90();
    assert k == 92;
    if 0 < y {
      ghost var g := this.70();
      this.567(y-1);
      assert g == 80;
    }
  }

  constructor 20_0(x: int)
  {
    new;
    var u := this.88;
    assert u == DigitUnderscore_Names_Functions_and_Methods.88;
  }

  static const 88: bool

  method 498() {
    var p := new DigitUnderscore_Names_Functions_and_Methods.20_0(200);
    p.567(100);
  }

  least predicate 500(y: int)
  {
    y == 0 || this.500(y-1)
  }

  least lemma 5_0_0(y: int)
    requires this.500(y)
    ensures 0 <= y
  {
  }
  lemma Another(k: ORDINAL, y: int)
    requires this.500#[k](y)
    ensures 0 <= y
  {
    this.5_0_0#[k](y);
  }

  const x' := 3.0  // the prime in the name previously compiled incorrectly
  method Regression(u: real) returns (v: real)
  {
    v := u * x';
  }
}

// -------------------------------------------------
// once buggy for method calls

module TypeInstantiations {
  function F<G>(): int { 56 }
  function H<G>(g: G): int { 57 }
  method M<G>() returns (r: int) { r := 100; }
  method N<G>(g: G) returns (r: int) { r := 101; }

  class GenCl<U> {
    static function Static<G>(): int { 58 }
    function Inst<G>(): int { 59 }
    static method Ms<G>() returns (r: int) { r := 102; }
    method Mi<G>() returns (r: int) { r := 103; }
  }

  method TestMain() {
    var x := F<char>();
    var ch: char := *;
    var y := H(ch);
    print x, " ", y, "\n";

    var a0 := GenCl<char>.Static<real>();
    var cl := new GenCl<char>;
    var a1 := cl.Inst<real>();
    print a0, " ", a1, "\n";

    x := M<char>();
    y := N(ch);
    print x, " ", y, "\n";

    a0 := GenCl<char>.Ms<real>();
    a1 := cl.Mi<real>();
    print a0, " ", a1, "\n";
  }
}

// -------------------------------------------------
// once buggy -- tail recursion where type parameters change

module TailRecursionWhereTypeParametersChange {
  method TestMain() {
    Compute<real>(5);  // expected output: 0.0 False False
  }

  // Ostensibly, this looks like a tail recursive method. However, a
  // recursive call that changes the type arguments cannot be compiled
  // using a tail-recursive goto. Therefore, this method is rejected
  // as tail recursive (which means that, for a large enough "n", it
  // can run out of stack space).
  method Compute<G(0)>(n: nat)
  {
    if n == 0 {
      print "\n";
    } else if n % 2 == 0 {
      Compute<bool>(n-1);
    } else {
      var g: G := *;
      print g, " ";
      Compute<G>(n-1);
    }
  }
}

// -------------------------------------------------

module GeneralMaps {
  method Test() {
    var m := map x {:nowarn} | 2 <= x < 6 :: x+1;
    PrintMap(m, 0, 20);
    m := map y {:nowarn} | 2 <= y < 6 :: y+1 := y+3;
    PrintMap(m, 0, 20);
    m := map y {:nowarn} | 2 <= y < 6 :: y+1 := 10;
    PrintPairs(m.Items, 0, 20);
    print m.Keys, "\n";
    print m.Values, "\n";
  }

  method PrintMap(m: map<int, int>, lo: int, hi: int)
    requires lo <= hi
  {
    print |m|, ": map[";
    var sep := "";
    for i := lo to hi {
      if i in m.Keys {
        print sep, i, " := ", m[i];
        sep := ", ";
      }
    }
    print "]\n";
  }

  method PrintPairs(pairs: set<(int, int)>, lo: int, hi: int)
    requires lo <= hi
  {
    print |pairs|, ": {";
    var sep := "";
    for i := lo to hi {
      for j := lo to hi {
        if (i, j) in pairs {
          print sep, (i, j);
          sep := ", ";
        }
      }
    }
    print "}\n";
  }
}

// -------------------------------------------------

module Cardinalities {
  method Test() {
    var s := "hello";
    var q := [0, 2, 4];
    var t := {s};
    var m := multiset{3, 5, 3};
    var p := map[false := s, true := s];
    print |s|, " ", |q|, " ", |t|, " ", |m|, " ", |p|, "\n";
  }
}

// -------------------------------------------------

module AltLoop {
  method Test() {
    var m, n := 5, 2;
    while
      decreases m + n
    {
      case 0 < n =>
        print n, " ";
        n := n - 1;
      case n == 0 < m =>
        print m, " ";
        m := m - 1;
    }
    print "\n";
  }
}
