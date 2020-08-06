// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
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
  print c.cell, " ", c.cell.data, " ", c.cell.Cell?, "\n";  // Cell.Cell(false) false true

  var x0: ();
  var x4: (int, bool, bool, seq<real>);
  print x0, " ", x4, "\n";  // () (0, false, false, [])

  var null2: (SomeObject?, Cell<int>);
  var null2': (SomeObject?, Cell<int>);
  print null2, " ", null2', " ", null2 == null2', "\n";  // (null, Cell.Cell(0)) (null, Cell.Cell(0)) true
  var null4: (SomeObject?, Class?, WClass?<bool>, Cell<int>);
  var null4': (SomeObject?, Class?, WClass?<bool>, Cell<int>);
  print null4, " ", null4', " ", null4 == null4', "\n";  // (null, null, null, Cell.Cell(0)) (null, null, null, Cell.Cell(0)) true
  print c == c, " ", c == null4.1, " ", null4.1 == c, " ", null4.1 == null, "\n";  // true false false true
  print Same(c, c), " ", Same(c, null4.1), " ", Same(null4.1, c), " ", Same(null4.1, null), "\n";  // true false false true

  // this will compute some hash codes
  var m: map<(SomeObject?, Cell<int>), int>;  // auto initialized
  m := m[null2 := 15];
  m := m[null2' := 17];
  print m[null2], "\n";  // 17
  More();
  Arrows();
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
