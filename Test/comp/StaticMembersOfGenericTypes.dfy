// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  GenericClass();
  FunctionValues();
  Coercions();
}

// ------------------------------------------------------------

method GenericClass() {
  var bb, aa, gg, hh, f2, f3;
  f2 := (x, y) => (x, y);
  f3 := (x, y, z) => (x, y, z);
  print f2(0, 1), " ", f3(true, 2, 3), "\n";

  // class membes
  bb, aa := Class.M(22, 23);
  f2 := Class.F;
  print Class<int>.K, " ", Class<int>.N, " ", Class.F(20, 21), " ", f2(20, 21), " ", bb, " ", aa, "\n";

  // datatype members
  bb, aa := Datatype.M(22, 23);
  f2 := Datatype.F;
  print Datatype<int>.K, " ", Datatype<int>.N, " ", Datatype.F(20, 21), " ", f2(20, 21), " ", bb, " ", aa, "\n";

  // trait members
  gg, hh, bb := Trait.M'(true, 22, 23);
  f3 := Trait.F';
  print Trait<int, int>.K', " ", Trait<int, int>.N', " ", Trait.F'(true, 20, 21), " ", f3(true, 20, 21), " ", gg, " ", hh, " ", bb, "\n";

  // trait members referenced via class
  gg, hh, bb := Class.M'(true, 22, 23);
  f3 := Class.F';
  print Class<int>.K', " ", Class<int>.N', " ", Class.F'(true, 20, 21), " ", f3(true, 20, 21), " ", gg, " ", hh, " ", bb, "\n";

  // now, try the same thing, but using a receiver value whose static type says where to find the member
  var c := new Class<int>;
  var t: Trait := c;
  var d: Datatype<int>;

  // class membes
  bb, aa := c.M(22, 23);
  f2 := c.F;
  print c.K, " ", c.N, " ", c.F(20, 21), " ", f2(20, 21), " ", bb, " ", aa, "\n";

  // datatype members
  bb, aa := d.M(22, 23);
  f2 := d.F;
  print d.K, " ", d.N, " ", d.F(20, 21), " ", f2(20, 21), " ", bb, " ", aa, "\n";

  // trait members
  gg, hh, bb := t.M'(true, 22, 23);
  f3 := t.F';
  print t.K', " ", t.N', " ", t.F'(true, 20, 21), " ", f3(true, 20, 21), " ", gg, " ", hh, " ", bb, "\n";

  // trait members referenced via class
  gg, hh, bb := c.M'(true, 22, 23);
  f3 := c.F';
  print c.K', " ", c.N', " ", c.F'(true, 20, 21), " ", f3(true, 20, 21), " ", gg, " ", hh, " ", bb, "\n";
}

trait Trait<G, H(0)> {
  static const K': H
  static const N' := 25
  static function F'<B>(g: G, h: H, b: B): (G, H, B) {
    (g, h, b)
  }
  static method M'<B>(g: G, h: H, b: B) returns (gg: G, hh: H, bb: B) {
    gg, hh, bb := g, h, b;
  }
}

class Class<A(0)> extends Trait<bool, A> {
  static const K: A
  static const N := 25
  static function F<B>(a: A, b: B): (A, B) {
    (a, b)
  }
  static method M<B>(a: A, b: B) returns (bb: B, aa: A) {
    bb, aa := b, a;
  }
}

datatype Datatype<A(0)> = Something {
  static const K: A
  static const N := 25
  static function F<B>(a: A, b: B): (A, B) {
    (a, b)
  }
  static method M<B>(a: A, b: B) returns (bb: B, aa: A) {
    bb, aa := b, a;
  }
}

// --------------------

method FunctionValues() {
  var c := new ClassFunc;
  var t: TraitFunc := c;
  var d := DFMake(18.0);
  var n: NewtypeFunc := 9;

  {
    var h := ClassFunc.F;
    var k := c.G;
    print h(2.0, true), " ", k(3.0, false), "\n";
  }

  {
    var h := DatatypeFunc.F;
    var k := d.G;
    print h(2.0, true), " ", k(3.0, false), "\n";
  }

  {
    var h := NewtypeFunc.F;
    var k := n.G;
    print h(true), " ", k(false), "\n";
  }

  {
    var f0, f1, g;
    f0, f1, g := TraitFunc.F', t.F', t.G';
    print f0(5, 2.0, true), " ", f1(5, 2.0, true), " ", g(6, 3.0, false), "\n";

    f0, f1, g := ClassFunc.F', c.F', c.G';
    print f0(5, 2.0, true), " ", f1(5, 2.0, true), " ", g(6, 3.0, false), "\n";
  }
}

trait TraitFunc<X(0), Y> {
  static function F'<U>(x: X, y: Y, u: U): (X, Y, U) {
    (x, y, u)
  }
  function G'<U>(x: X, y: Y, u: U): (X, Y, U) {
    (x, y, u)
  }
}

class ClassFunc<T> extends TraitFunc<int, T> {
  static function F<U>(t: T, u: U): (T, U) {
    (t, u)
  }
  function G<U>(t: T, u: U): (T, U) {
    (t, u)
  }
}

datatype DatatypeFunc<T> = DFMake(T) {
  static function F<U>(t: T, u: U): (T, U) {
    (t, u)
  }
  function G<U>(t: T, u: U): (T, U) {
    (t, u)
  }
}

newtype NewtypeFunc = x | 0 <= x < 25 {
  static function F<U>(u: U): U {
    u
  }
  function G<U>(u: U): U {
    u
  }
}

// ------------------------------------------------------------

method Coercions() {
  var c := new Coer<int>(50);
  var y: int;
  y := c.x;
  c.x := y;
  y := c.m;

  var z := Id(y);
  var plus := u => u + 1;
  var p := Id(plus);
  var q := IdFunc(plus);
  print z, " ", p(2), " ", q(3), "\n";  // 50 3 4
  print c.x + Id(Id(plus))(48) + Id(y), "\n";  // 149
}

function Id<G>(g: G): G { g }

function IdFunc<H>(h: H -> H): H -> H { h }

class Coer<T> {
  constructor (u: T) {
    x := u;
    m := u;
  }
  var x: T
  var m: T
}
