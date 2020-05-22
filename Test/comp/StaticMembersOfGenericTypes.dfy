// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cs "%s" > "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  GenericClass();
}

// ------------------------------------------------------------

method GenericClass() {
  var bb, aa, gg, hh, f2, f3;
  f2 := (x, y) => (x, y);
  f3 := (x, y, z) => (x, y, z);

  // class membes
  bb, aa := Class.M(22, 23);
//  f2 := Class.F;
  print Class<int>.K, " ", Class<int>.N, " ", Class.F(20, 21), " ", f2(20, 21), " ", bb, " ", aa, "\n";

  // datatype members
  bb, aa := Datatype.M(22, 23);
//  f2 := Datatype.F;
  print Datatype<int>.K, " ", Datatype<int>.N, " ", Datatype.F(20, 21), " ", f2(20, 21), " ", bb, " ", aa, "\n";

  // trait members
  gg, hh, bb := Trait.M'(true, 22, 23);
//  f3 := Trait.F';
  print Trait<int, int>.K', " ", Trait<int, int>.N', " ", Trait.F'(true, 20, 21), " ", f3(true, 20, 21), " ", gg, " ", hh, " ", bb, "\n";

  // trait members referenced via class
  gg, hh, bb := Class.M'(true, 22, 23);
//  f3 := Class.F';
  print Class<int>.K', " ", Class<int>.N', " ", Class.F'(true, 20, 21), " ", f3(true, 20, 21), " ", gg, " ", hh, " ", bb, "\n";

  // now, try the same thing, but using a receiver value whose static type says where to find the member
  var c := new Class<int>;
  var t: Trait := c;
  var d: Datatype<int>;

  // class membes
  bb, aa := c.M(22, 23);
//  f2 := c.F;
  print c.K, " ", c.N, " ", c.F(20, 21), " ", f2(20, 21), " ", bb, " ", aa, "\n";

  // datatype members
  bb, aa := d.M(22, 23);
//  f2 := d.F;
  print d.K, " ", d.N, " ", d.F(20, 21), " ", f2(20, 21), " ", bb, " ", aa, "\n";

  // trait members
  gg, hh, bb := t.M'(true, 22, 23);
//  f3 := t.F';
  print t.K', " ", t.N', " ", t.F'(true, 20, 21), " ", f3(true, 20, 21), " ", gg, " ", hh, " ", bb, "\n";

  // trait members referenced via class
  gg, hh, bb := c.M'(true, 22, 23);
//  f3 := c.F';
  print c.K', " ", c.N', " ", c.F'(true, 20, 21), " ", f3(true, 20, 21), " ", gg, " ", hh, " ", bb, "\n";
}

trait Trait<G, H(0)> {
  static const K': H
  static const N' := 25
  static function method F'<B>(g: G, h: H, b: B): (G, H, B) {
    (g, h, b)
  }
  static method M'<B>(g: G, h: H, b: B) returns (gg: G, hh: H, bb: B) {
    gg, hh, bb := g, h, b;
  }
}

class Class<A(0)> extends Trait<bool, A> {
  static const K: A
  static const N := 25
  static function method F<B>(a: A, b: B): (A, B) {
    (a, b)
  }
  static method M<B>(a: A, b: B) returns (bb: B, aa: A) {
    bb, aa := b, a;
  }
}

datatype Datatype<A(0)> = Something {
  static const K: A
  static const N := 25
  static function method F<B>(a: A, b: B): (A, B) {
    (a, b)
  }
  static method M<B>(a: A, b: B) returns (bb: B, aa: A) {
    bb, aa := b, a;
  }
}
