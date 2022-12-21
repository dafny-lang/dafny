// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// This file tests the compilation of some default values. It also includes some
// regression tests for equality, printing, and tuples.

codatatype Stream<G> = Next(head: G, tail: Stream<G>)

class WClass<W> {
  const strm: Stream<W>
  var pair: (bool, int)
  constructor Make(w: W) {
    strm := Generate(w);
  }
  static function method Generate(w: W): Stream<W> {
    Next(w, Generate(w))
  }
}

datatype Cell<T> = Cell(data: T)

class SomeObject { }

class Class {
  var cell: Cell<bool>
  var obj: SomeObject
  constructor () {
    obj := new SomeObject;
  }
}

predicate method Same<A(==)>(a0: A, a1: A) {
  a0 == a1
}

method Main() {
  var w := new WClass<bv8>.Make(3);
  print w.strm.tail.head, " ", w.pair.0, " ", w.pair.1, "\n";  // 3 false 0

  var c := new Class();
  print c.cell, " ", c.cell.data, " ", c.cell.Cell?, "\n";  // false false true

  var x0: ();
  var x4: (int, bool, bool, seq<real>);
  print x0, " ", x4, "\n";  // () (0, false, false, [])

  var null2: (SomeObject?, Cell<int>);
  var null2': (SomeObject?, Cell<int>);
  print null2, " ", null2', " ", null2 == null2', "\n";  // (null, 0) (null, 0) true
  var null4: (SomeObject?, Class?, WClass?<bool>, Cell<int>);
  var null4': (SomeObject?, Class?, WClass?<bool>, Cell<int>);
  print null4, " ", null4', " ", null4 == null4', "\n";  // (null, null, null, 0) (null, null, null, 0) true
  print c == c, " ", c == null4.1, " ", null4.1 == c, " ", null4.1 == null, "\n";  // true false false true
  print Same(c, c), " ", Same(c, null4.1), " ", Same(null4.1, c), " ", Same(null4.1, null), "\n";  // true false false true

  // this will compute some hash codes
  var m: map<(SomeObject?, Cell<int>), int>;  // auto initialized
  m := m[null2 := 15];
  m := m[null2' := 17];
  print m[null2], "\n";  // 17
  More();
  Arrows();
  NilRegression.Test();
  DatatypeDefaultValues.Test();
  ImportedTypes.Test();
  GhostWitness.Test();
}

datatype ThisOrThat<A,B> = This(A) | Or | That(B)
type pos = i: nat | i != 0 witness 1
type OrThat<X> = tot: ThisOrThat<X, int> | !tot.This? witness Or
newtype OddByte = i | 2 <= i < 20 && i % 2 == 1 witness 3
newtype OddNat = i | 4 <= i && i % 2 == 1 witness 9

method More() {
  var x: pos;
  var y: OddByte;
  var z: OddNat;
  var w: bv7;
  var v: bv2009;
  var u: ThisOrThat<bool, real>;
  var t: OrThat<bv5>;
  print x, " ", y, " ", z, " ", w, " ", v, " ", u, " ", t, "\n"; // 1 3 9 0 0 ThisOrThat.Or ThisOrThat.Or
  var p: (pos, OddByte, OddNat, bv7, bv2009, ThisOrThat<bool, real>, OrThat<bv5>); // (1, 3, 9, 0, 0, ThisOrThat.Or, ThisOrThat.Or)
  print p, "\n";
}

method Arrows() {
  var f: int -> pos;
  var g: int --> pos;
  var h: int ~> pos;

  DoNothing(f);
  DoNothing(g);
  DoNothing(h);
  print f(2), "\n";  // 1
}

method DoNothing(F: int ~> pos) { }

module NilRegression {
  trait Trait { }
  class Class extends Trait { }

  method Test() {
    NilRegression0();
    NilRegression1();
    var c: Class? := new Class;
    NilRegression2(c);
    NilRegression2(null);
    NilRegression3();
  }

  method NilRegression0() {
    var uu: Class?;
    if uu != null {
      uu := null;
    }
    assert uu == null;
    var ww: object? := uu;
    assert ww == null;
    if ww == null {
      print "ww == null  -- yes, as expected\n";
    } else {
      assert false;
      print "ww != null  -- impossible!\n";
    }
  }

  method NilRegression1() {
    var c: Class? := null;
    var t: Trait? := null;
    var u: Trait? := c;
    var w := c == c;
    var x := t == c;
    var y := t == t;
    var z := t == u;
    print w, " ", x, " ", y, " ", z, "\n";  // true true true true
  }

  method NilRegression2(cc: Class?) {
    var tt: Trait? := cc;
    tt := cc;
    var oo: object? := cc;
    oo := tt;

    var a := cc == tt;
    var b := cc == oo;
    var c := tt == oo;

    var x := cc == cc;
    var y := tt == tt;
    var z := oo == oo;

    print a, " ", b, " ", c, "\n";  // true true true
  }

  class GClass<U(0), V(0), W(0)> {
    var u: U
    var v: V
    var w: W

    const u': U
    const v': V
    const w': W

    var u1: array<U>
    var v1: array<V>
    var w1: array<W>

    var u2: array2<U>
    var v2: array2<V>
    var w2: array2<W>

    constructor ()
      ensures u1.Length == v1.Length == w1.Length == 1
      ensures u2.Length0 == v2.Length0 == w2.Length0 == 1
      ensures u2.Length1 == v2.Length1 == w2.Length1 == 1
    {
      u1, v1, w1 := new U[1], new V[1], new W[1];
      u2, v2, w2 := new U[1, 1], new V[1, 1], new W[1, 1];
    }
  }

  datatype DaTy<X> = DaTy(get: X)
  datatype DaTy2<X> = Nothing | DaTy2(get: X)

  class MyClass { }

  method Gimmie<R(0)>() returns (r: R) { }
  method Gimmie2<R(0), S(0)>() returns (r: R, s: S) { }

  function method Id<X>(x: X): X { x }

  method NilRegression3() {
    // test out-parameters of methods
    var x0: object? := Gimmie();
    var x1: Trait? := Gimmie();
    print x0, " ", x1, "\n";
    x0, x1 := Gimmie2();
    print x0, " ", x1, "\n";

    // test fields
    var c := new GClass<object?, Trait?, MyClass?>();
    var u: object? := c.u;
    var v: Trait? := c.v;
    var w: MyClass? := c.w;
    print u, " ", v, " ", w, "\n";
    u, v, w := c.u', c.v', c.w';
    print u, " ", v, " ", w, "\n";

    // test arrays
    u, v, w := c.u1[0], c.v1[0], c.w1[0];
    print u, " ", v, " ", w, "\n";
    u, v, w := c.u2[0, 0], c.v2[0, 0], c.w2[0, 0];
    print u, " ", v, " ", w, "\n";

    // make sure casts can be in the middle of an expression
    var x: Trait? := if u == v then c.v else (((c.v)));
    // test result of functions
    var y: Trait? := Id(x);
    print x, " ", y, "\n";

    // test datatype destructors
    u, v, w := DaTy(u).get, DaTy(v).get, DaTy(w).get;
    print u, " ", v, " ", w, "\n";
    u, v, w := DaTy2(u).get, DaTy2(v).get, DaTy2(w).get;
    print u, " ", v, " ", w, "\n";
  }
}

module DatatypeDefaultValues {
  datatype EnumDatatype = MakeZero | MakeOne
  datatype IntList = Nil | Cons(int, IntList)
  datatype Cell<B> = MakeCell(B)
  datatype GenericTree<A> = Leaf | Node(GenericTree<A>, GenericTree<A>)
  datatype Complicated<K, L(0), M, N(0)> = ComplA(K, L) | Rest(Complicated<K, L, M, N>)
  datatype CellCell<X, Y> = MakeCellCell(Cell<X>) | MakeMoreCellCell(CellCell<X, Y>)

  datatype Difficult = MakeDifficult(Class?)
  datatype GenDifficult<G> = MakeGenDifficult(GenClass?<G>)
  class Class { }
  class GenClass<H> { }

  method Test() {
    var a: EnumDatatype;
    var b: IntList;
    var c: Cell<int>;
    var d: GenericTree<int>;
    var e: Complicated<int, bool, real, bv3>;
    var f: CellCell<int, real>;
    print a, "\n  ", b, "\n  ", c, "\n"; // MakeZero Nil 0
    print d, "\n  ", e, "\n  ", f, "\n"; // Leaf ComplA(0, false) MakeCellCell(0)

    var g: Difficult;
    var h: GenDifficult<int>;
    print g, "\n  ", h, "\n"; // null null
  }
}

module ImportedTypes {
  module Library {
    datatype Color = Red(int) | Green(real) | Blue(bv30)
    codatatype CoColor = Yellow(int)
    codatatype MoColor = MoYellow(int, MoColor)
    newtype Nt = r | -1.0 <= r <= 1.0
  }

  method Test() {
    var c: Library.Color;
    Try(c);

    var co: Library.CoColor;
    Try(co);
    var mo: Library.MoColor;
    Try(mo);

    var nt: Library.Nt;
    Try(nt);
  }

  method Try<A(0)>(a: A) {
    var x: A;
    print a, " and ", x, "\n";
  }
}

module GhostWitness {
  type EffectlessArrow<!A(!new), B(00)> = f: A ~> B
    | forall a :: f.reads(a) == {}
    ghost witness GhostEffectlessArrowWitness<A, B>

  function GhostEffectlessArrowWitness<A, B(00)>(a: A): B
  {
    var b: B :| true; b
  }

  codatatype Forever = More(Forever)

  class MyClass { }

  predicate Total<A(!new), B>(f: A ~> B)  // (is this (!new) really necessary?)
    reads f.reads
  {
    forall a :: f.reads(a) == {} && f.requires(a)
  }

  type TotalArrow<!A(!new), B(00)> = f: EffectlessArrow<A, B>
    | Total(f)
    ghost witness TotalWitness<A, B>

  function TotalWitness<A, B(00)>(a: A): B
  {
    var b: B :| true; b
  }

  method Test() {
    var g: EffectlessArrow<int, int>;
    var f: TotalArrow<int, int>;
    f := y => y + 2;
    g := f;
    var x := g(4) + f(5);
    print x, "\n";
  }
}
