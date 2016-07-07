// RUN: %dafny /compile:3 /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

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

  function method AscendingChain(n: int): Stream<int>
  {
    More(n, AscendingChain(n+1))
  }

  datatype List<T> = Nil | Cons(car: T, cdr: List)

  function method Prefix(n: nat, s: Stream): List
  {
    if n == 0 then Nil else
    Cons(s.head, Prefix(n-1, s.rest))
  }

  class Cell { var data: int; }

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
      decreases l;
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
    if y :| lo < y < hi {
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
      case y :| lo < y < hi =>
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
    var f: int;
    method m()
  }
}

module T refines S {
  class C {
    method m() {
      print "in T.C.m()";
    }
  }
}
module A {
   import X : T
   import Y : T
   import Z = T
   method run() {
     var x := new X.C;
     x.m();
     var y := new Y.C;
     y.m();
     var z := new Z.C;
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
module A1 {
   import X : T1
   method run() {
     X.do();
     var x := new X.B.C;
     x.m();
   }
}

// ----- keyword escapes (once buggy) -----

module M {
  datatype fixed = A | B
  function method F(): fixed
  {
    A
  }
  class public {
    var private: int;
  }
}

method Caller() {
  var p := new M.public;
  var x := p.private;
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
  var 7: bool;
  method M(c: DigitsClass)
    requires c != null;
  {
    var x: int := if this.7 then 7 else if c.7 then 8 else 9;
  }
}

// Should not get errors about methods or functions with empty bodies
// if they're marked with an :axiom attribute
ghost method {:axiom} m_nobody() returns (y:int)
  ensures y > 5;

lemma {:axiom} l_nobody() returns (y:int)
  ensures y > 5;

function {:axiom} f_nobody():int 
  ensures f_nobody() > 5;

// Make sure the lemma created for opaque functions doesn't produce compiler errors
function {:opaque} hidden():int
{
  7
}

method hidden_test()
{
  reveal_hidden();
  assert hidden() == 7;
}

// ----- LetExpr with ghosts and in ghost contexts -----

module GhostLetExpr {
  method M() {
    ghost var y;
    var x;
    var g := G(x, y);
    ghost var h := var ta := F(); 5;
    var j := ghost var tb := F(); 5;
    assert h == j;
  }

  function F(): int
  { 5 }

  function method G(x: int, ghost y: int): int
  { assert y == y; x }

  datatype Dt = MyRecord(a: int, ghost b: int)

  method P(dt: Dt) {
    match dt {
      case MyRecord(aa, bb) =>
        ghost var z := bb + F();
        ghost var t0 := var y := z; z + 3;
        ghost var t1 := ghost var y := z; z + 3;
        var t2 := ghost var y := z; aa + 3;
    }
  }

  function method FM(): int
  {
    ghost var xyz := F();
    G(5, xyz)
  }
}

class DigitUnderscore_Names {
  // the following would be the same integers, but they are different fields
  var 0_1_0: int;
  var 010: int;
  var 10: int;
  // ... as we see here:
  method M()
    modifies this;
  {
    this.0_1_0 := 007;
    this.010 := 000_008;
    this.10 := 0x0000_0009;
    assert this.0_1_0 == int(00_07.0_0) && this.010 == 8 && this.10 == 9;
    this.10 := 20;
  }
}

// ------------------------------------------------------------------

method Main()
{
  CoRecursion.TestMain();
  EqualityTests.TestMain();
}

// ------------------------------------------------------------------

module EqualityTests {
  class C<T> {
  }

  method TestMain()
  {
    // regression tests:
    var a: C<int>, b: C<int> := null, null;
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

  method ArrayTests<T>(H: array<T>)
  {
    var G := new int[10];
    if G == H {  // this comparison is allowed in Dafny, but requires a cast in C#
      print "this would be highly suspicious\n";
    }
    if G != H {  // this comparison is allowed in Dafny, but requires a cast in C#
      print "good world order\n";
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
