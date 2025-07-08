// RUN: %testDafnyForEachCompiler "%s" -- --type-system-refresh=true --general-traits=datatype

method Main() {
  As.Test();
  Is.Test();
  Basic.Test();
  Bounds.Test();
  BoundsAndCasts.Test();
  Conversions.Test();
  Operators.Test();
  ReturnExpr.Test();
}

module As {
  trait Parent {
    const k: int
  }
  trait Trait extends Parent { }
  class Class extends Trait {
    constructor (n: int) {
      k := n;
    }
  }

  method Test() {
    var c := new Class(14);
    M(c);
    var b := N(c);
    O(c);
    P(c);
  }
  
  method M<X extends Trait>(x: X) {
    var a0 := x as X;
    var a1 := x as Trait;
    var a2 := x as Parent;
    print a1.k, " "; // 14
  }

  method N<X(==) extends Trait>(x: X) returns (b: bool) {
    var t: Trait := x as Trait;
    b := x == t as X;
    print b, " "; // true
  }

  method O<Z extends object?>(z: Z) {
    var a := z as object?;
    print a != null, " "; // true
  }

  method P<Z extends object>(z: Z) {
    var a := z as object?;
    var b := z as object;
    print b == a != null, "\n"; // true
  }
}

module Is {
  trait Parent {
    const k: int
  }
  trait Trait extends Parent { }
  class Class extends Trait {
    constructor (n: int) {
      k := n;
    }
  }

  method Test() {
    var c := new Class(14);
    M(c);
    O(c); // true true
    O(null); // true false
    P(c);
  }
  
  method M<X extends Trait>(x: X) {
    print x is X, " "; // true
    print x is Trait, " "; // true
    print x is Parent, " "; // true
    print (x as Trait) is Class, "\n"; // false
  }

  method O<Z extends object?>(z: Z) {
    print z is object?, " ";
    print z is object, " ";
  }

  method P<Z extends object>(z: Z) {
    print z is object?, " "; // true
    print z is object, "\n"; // true
  }
}

module Basic {
  trait Parent extends object {
    const k: int
  }
  trait Trait extends Parent { }
  class Class extends Trait {
    constructor (n: int) {
      k := n;
    }
  }

  method TestMethod<X extends Trait? extends Parent>(x: X) returns (obj: object?)
    ensures obj != null
  {
    var b := x is Trait;
    assert b;
    print b, " "; // true

    b := x is Parent;
    assert b;
    print b, " "; // true

    var t: Trait := x as Trait;
    obj := t;
  }

  method Test() {
    var c := new Class(18);
    var obj := TestMethod(c);
    print obj != null, "\n"; // true
  }
}

module Bounds {
  trait Trait<X> {
    function Value(): X
  }

  datatype Dt extends Trait<string> = Dt(s: string)
  {
    function Value(): string { s }
  }

  method MyMethod<Y extends Trait<string>>(y: Y) {
    var s := (y as Trait<string>).Value();
    print "(", s, ")\n";
  }

  class RandomClass<R> extends Trait<R> {
    const r: R
    constructor (r: R) {
      this.r := r;
    }
    function Value(): R { r }
  }

  method Test() {
    var d := Dt("hello");
    MyMethod(d);

    var c := new RandomClass("you don't say");
    MyMethod(c);

    var v := *; // inferred to be of type string (pretty cool, huh!)
    var i := new RandomClass(v);
    MyMethod(i);
  }
}

module BoundsAndCasts {
  method Test() {
    var rx := Record("X thing");
    var ry := Record("Y thing");
    var rp := Record("P thing");
    var d := Dt(rx);
    d.M(ry, rp);
    print d.F(ry, rp), "\n";
    print d.K(rp), "\n";
  }

  trait Parent { }
  trait XTrait extends Parent { }
  trait YTrait extends Parent { }

  datatype Record extends XTrait, YTrait = Record(s: string)

  datatype Dt<X extends XTrait> = Dt(x: X)
  {
    method M<Y extends YTrait>(y: Y, p: X) {
      var parent: Parent;

      parent := x;
      print parent, "\n";
      assert parent is XTrait;

      parent := p;
      assert parent is XTrait;
      print parent, "\n";

      parent := y;
      assert parent is YTrait;
      print parent, "\n";
    }

    function F<Y extends YTrait>(y: Y, p: X): int {
      var parentX: Parent := x;
      assert parentX is XTrait;
      var parentP: Parent := p;
      assert parentP is XTrait;
      var parentY: Parent := y;
      assert parentY is YTrait;
      15
    }

    const K := (p: X) =>
      var parentX: Parent := x;
      assert parentX is XTrait;
      var parentP: Parent := p;
      assert parentP is XTrait;
      17
  }
}

module Conversions {
  trait Trait {
    function F(): int
  }

  datatype Dt extends Trait = Dt(u: int) {
    function F(): int {
      u
    }
  }

  datatype Covariant<+X> = Make(value: X)

  method TestCovarianceZ<Z extends Trait>(z: Z) {
    var h: Covariant<Z> := Covariant<Z>.Make(z);

    var g: Covariant<Trait>;
    g := h;
    g := h as Covariant<Trait>;
    print (z as Trait).F(), " ", g, " ", h, "\n"; // 5 Dt.Dt(5) Dt.Dt(5)
  }

  method Test() {
    var d := Dt(5);
    TestCovarianceZ(d);
  }
}

module Operators {
  trait Trait extends object { }

  method P8<Z extends Trait>(z: Z, t: Trait) returns (s: seq<Trait>) {
    s := [z];
    s := [z as Trait, t];
    s := s[0 := z];
    s := s[0 := z as Trait];
    var zt: Trait := s[0];
  }

  method P9<Z(==) extends Trait>(z: Z, t: Trait) returns (m: map<Trait, Trait>, mi: map<Trait, Trait>) {
    m := map[z := z];
    m := m[z as Trait := z as Trait]; // TODO: these casts should not be needed
    mi := map[z := z];
    mi := mi[z as Trait := z as Trait]; // TODO: these casts should not be needed

    m := map[z as Trait := t];
    m := m[z as Trait := t];
    mi := map[z as Trait := t];
    mi := mi[z as Trait := t];

    m := map[t := z as Trait];
    m := m[t := z as Trait];
    mi := map[t := z as Trait];
    mi := mi[t := z as Trait];

    var zt: Trait := m[t];
    zt := mi[t];
  }

  method P10<Z(==) extends Trait>(z: Z, t: Trait) returns (m: multiset<Trait>) {
    m := multiset{z, z};
    m := multiset{z as Trait, t}; // TODO: this cast should not be needed
    m := m[z as Trait := 13]; // TODO: this cast should not be needed

    var count := m[z];
    count := m[t];
  }

  class CC extends Trait { }

  method Test() {
    var cc := new CC;
    var _ := P8(cc, cc);
    var _, _ := P9(cc, cc);
    var _ := P10(cc, cc);
    print "done\n";
  }
}

module ReturnExpr {
  trait Trait {}

  function F<X extends Trait>(x: X): Trait {
    assert x is Trait;
    x
  }

  function G<X extends Trait>(x: X): Trait {
    x as Trait
  }

  trait ReferenceTrait extends object {}

  function H<X extends ReferenceTrait>(x: X): ReferenceTrait {
    assert x is ReferenceTrait;
    x
  }

  class C extends Trait, ReferenceTrait {
  }

  method Test() {
    var c := new C;
    for i := 0 to 2 {
      var t: Trait := if i == 0 then F(c) else G(c);
      assert c == t;
      var tc: C := t as C;
      expect c == tc;
    }

    var h: ReferenceTrait := H(c);
    expect c == h;
  }
}
