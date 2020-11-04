// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  Methods.TestStart();
  Functions.TestStart();
  Consts.TestStart();
}

module Methods {
  newtype Newtype = x | 0 <= x < 500 {
    method InstanceN<B(0)>(b: B) returns (bb: B) { }
    static method StaticN<B(0)>(b: B) returns (bb: B) { }
  }

  datatype Datatype<A(0)> = Dt0 | Dt1 {
    method InstanceD<B(0)>(a: A, b: B) returns (aa: A, bb: B) { }
    static method StaticD<B(0)>(a: A, b: B) returns (aa: A, bb: B) { }
  }

  trait UberTrait<A(0)> {
    method InstanceU0<B(0)>(a: A, b: B) returns (aa: A, bb: B) { }
    method InstanceU1<B(0)>(a: A, b: B) returns (aa: A, bb: B)
    method InstanceU2<B(0)>(a: A, b: B) returns (aa: A, bb: B)
    method InstanceU3<B(0)>(a: A, b: B) returns (aa: A, bb: B)
  }

  trait InBetween<A(0)> extends UberTrait<A> {
    method InstanceU1<B(0)>(a: A, b: B) returns (aa: A, bb: B) { }
  }

  trait Trait<A(0)> extends InBetween<A> {
    method InstanceU2<B(0)>(a: A, b: B) returns (aa: A, bb: B) { }
    method InstanceT<B(0)>(a: A, b: B) returns (aa: A, bb: B)
    method InstanceTBody<B(0)>(a: A, b: B) returns (aa: A, bb: B) { }
    static method StaticT<B(0)>(a: A, b: B) returns (aa: A, bb: B) { }
  }

  class Class<A(0)> extends Trait<A> {
    method InstanceU3<B(0)>(a: A, b: B) returns (aa: A, bb: B) { }
    method InstanceT<B(0)>(a: A, b: B) returns (aa: A, bb: B) { }
    method InstanceC<B(0)>(a: A, b: B) returns (aa: A, bb: B) { }
    static method StaticC<B(0)>(a: A, b: B) returns (aa: A, bb: B) { }
  }

  datatype Uni = Uni

  method TestStart() {
    Test(Uni, Uni);
    Test([Uni], {2});
  }

  method Test<X(0), Y(0)>(x: X, y: Y) {
    var c: Class<X> := new Class<X>;
    var t: Trait<X> := c;
    var u: UberTrait<X> := c;
    var v: InBetween<X> := c;
    var d: Datatype<X> := Dt0;
    var n: Newtype := 100;
    var a, b;

    b := n.InstanceN<Y>(y);
    print b, "\n  ++ ";
    b := Newtype.StaticN<Y>(y);
    print b, "\n";

    a, b := d.InstanceD<Y>(x, y);
    print a, " ", b, "\n  ++ ";
    a, b := Datatype<X>.StaticD<Y>(x, y);
    print a, " ", b, "\n";

    a, b := u.InstanceU0<Y>(x, y);
    print a, " ", b, "\n  ++ ";
    a, b := u.InstanceU1<Y>(x, y);
    print a, " ", b, "\n  ++ ";
    a, b := u.InstanceU2<Y>(x, y);
    print a, " ", b, "\n  ++ ";
    a, b := u.InstanceU3<Y>(x, y);
    print a, " ", b, "\n";

    a, b := v.InstanceU0<Y>(x, y);
    print a, " ", b, "\n  ++ ";
    a, b := v.InstanceU1<Y>(x, y);
    print a, " ", b, "\n  ++ ";
    a, b := v.InstanceU2<Y>(x, y);
    print a, " ", b, "\n  ++ ";
    a, b := v.InstanceU3<Y>(x, y);
    print a, " ", b, "\n";

    a, b := t.InstanceU0<Y>(x, y);
    print a, " ", b, "\n  ++ ";
    a, b := t.InstanceU1<Y>(x, y);
    print a, " ", b, "\n  ++ ";
    a, b := t.InstanceU2<Y>(x, y);
    print a, " ", b, "\n  ++ ";
    a, b := t.InstanceU3<Y>(x, y);
    print a, " ", b, "\n";
    a, b := t.InstanceT<Y>(x, y);
    print a, " ", b, "\n  ++ ";
    a, b := t.InstanceTBody<Y>(x, y);
    print a, " ", b, "\n  ++ ";
    a, b := Trait<X>.StaticT<Y>(x, y);
    print a, " ", b, "\n";

    a, b := c.InstanceU0<Y>(x, y);
    print a, " ", b, "\n  ++ ";
    a, b := c.InstanceU1<Y>(x, y);
    print a, " ", b, "\n  ++ ";
    a, b := c.InstanceU2<Y>(x, y);
    print a, " ", b, "\n  ++ ";
    a, b := c.InstanceU3<Y>(x, y);
    print a, " ", b, "\n";
    a, b := c.InstanceT<Y>(x, y);
    print a, " ", b, "\n  ++ ";
    a, b := c.InstanceTBody<Y>(x, y);
    print a, " ", b, "\n  ++ ";
    a, b := c.InstanceC<Y>(x, y);
    print a, " ", b, "\n  ++ ";
    a, b := Class<X>.StaticC<Y>(x, y);
    print a, " ", b, "\n";
  }
}

module Functions {
  newtype Newtype = x | 0 <= x < 500 {
    function method InstanceN<B(0)>(b: B): B { b }
    static function method StaticN<B(0)>(b: B): B { b }
  }

  datatype Datatype<A(0)> = Dt0 | Dt1 {
    function method InstanceD<B(0)>(a: A, b: B): (A, B) { (a, b) }
    static function method StaticD<B(0)>(a: A, b: B): (A, B) { (a, b) }
  }

  trait UberTrait<A(0)> {
    function method InstanceU0<B(0)>(a: A, b: B): (A, B) { (a, b) }
    function method InstanceU1<B(0)>(a: A, b: B): (A, B)
    function method InstanceU2<B(0)>(a: A, b: B): (A, B)
    function method InstanceU3<B(0)>(a: A, b: B): (A, B)
  }

  trait InBetween<A(0)> extends UberTrait<A> {
    function method InstanceU1<B(0)>(a: A, b: B): (A, B) { (a, b) }
  }

  trait Trait<A(0)> extends InBetween<A> {
    function method InstanceU2<B(0)>(a: A, b: B): (A, B) { (a, b) }
    function method InstanceT<B(0)>(a: A, b: B): (A, B)
    function method InstanceTBody<B(0)>(a: A, b: B): (A, B) { (a, b) }
    static function method StaticT<B(0)>(a: A, b: B): (A, B) { (a, b) }
  }

  class Class<A(0)> extends Trait<A> {
    function method InstanceU3<B(0)>(a: A, b: B): (A, B) { (a, b) }
    function method InstanceT<B(0)>(a: A, b: B): (A, B) { (a, b) }
    function method InstanceC<B(0)>(a: A, b: B): (A, B) { (a, b) }
    static function method StaticC<B(0)>(a: A, b: B): (A, B) { (a, b) }
  }

  datatype Uni = Uni

  method TestStart() {
    Test(Uni, Uni);
    Test([Uni], {2});
  }

  method Test<X(0), Y(0)>(x: X, y: Y) {
    var c: Class<X> := new Class<X>;
    var t: Trait<X> := c;
    var u: UberTrait<X> := c;
    var v: InBetween<X> := c;
    var d: Datatype<X> := Dt0;
    var n: Newtype := 100;
    var b, p;

    b := n.InstanceN<Y>(y);
    print b, "\n  ++ ";
    b := Newtype.StaticN<Y>(y);
    print b, "\n";

    p := d.InstanceD<Y>(x, y);
    print p.0, " ", p.1, "\n  ++ ";
    p := Datatype<X>.StaticD<Y>(x, y);
    print p.0, " ", p.1, "\n";

    p := u.InstanceU0<Y>(x, y);
    print p.0, " ", p.1, "\n  ++ ";
    p := u.InstanceU1<Y>(x, y);
    print p.0, " ", p.1, "\n  ++ ";
    p := u.InstanceU2<Y>(x, y);
    print p.0, " ", p.1, "\n  ++ ";
    p := u.InstanceU3<Y>(x, y);
    print p.0, " ", p.1, "\n";

    p := v.InstanceU0<Y>(x, y);
    print p.0, " ", p.1, "\n  ++ ";
    p := v.InstanceU1<Y>(x, y);
    print p.0, " ", p.1, "\n  ++ ";
    p := v.InstanceU2<Y>(x, y);
    print p.0, " ", p.1, "\n  ++ ";
    p := v.InstanceU3<Y>(x, y);
    print p.0, " ", p.1, "\n";

    p := t.InstanceU0<Y>(x, y);
    print p.0, " ", p.1, "\n  ++ ";
    p := t.InstanceU1<Y>(x, y);
    print p.0, " ", p.1, "\n  ++ ";
    p := t.InstanceU2<Y>(x, y);
    print p.0, " ", p.1, "\n  ++ ";
    p := t.InstanceU3<Y>(x, y);
    print p.0, " ", p.1, "\n";
    p := t.InstanceT<Y>(x, y);
    print p.0, " ", p.1, "\n  ++ ";
    p := t.InstanceTBody<Y>(x, y);
    print p.0, " ", p.1, "\n  ++ ";
    p := Trait<X>.StaticT<Y>(x, y);
    print p.0, " ", p.1, "\n";

    p := c.InstanceU0<Y>(x, y);
    print p.0, " ", p.1, "\n  ++ ";
    p := c.InstanceU1<Y>(x, y);
    print p.0, " ", p.1, "\n  ++ ";
    p := c.InstanceU2<Y>(x, y);
    print p.0, " ", p.1, "\n  ++ ";
    p := c.InstanceU3<Y>(x, y);
    print p.0, " ", p.1, "\n";
    p := c.InstanceT<Y>(x, y);
    print p.0, " ", p.1, "\n  ++ ";
    p := c.InstanceTBody<Y>(x, y);
    print p.0, " ", p.1, "\n  ++ ";
    p := c.InstanceC<Y>(x, y);
    print p.0, " ", p.1, "\n  ++ ";
    p := Class<X>.StaticC<Y>(x, y);
    print p.0, " ", p.1, "\n";
  }
}

module Consts {
  datatype Datatype<A(0)> = Dt0(a: A) | Dt1(a: A) {
    const InstanceD0: A
    const InstanceD1: A := InstanceD0
    const InstanceD2: A := InstanceD3
    const InstanceD3: A := a
    const InstanceD4: A := InstanceD3
    static const StaticD0: A
    static const StaticD1: A := StaticD0
  }

  trait Trait<A(0)> {
    const InstanceT0: A
    const InstanceT1: A := InstanceT0
    const InstanceT2: A
    var VarT0: A
    var VarT1: A
    static const StaticT0: A
    static const StaticT1: A := StaticT0
  }

  class Class<A(0)> extends Trait<A> {
    const InstanceC0: A
    const InstanceC1: A := InstanceC0
    const InstanceC2: A := InstanceT0
    const InstanceC3: A
    var VarC0: A
    var VarC1: A
    constructor (a: A) {
      InstanceT0 := a;
      VarT0 := a;
      // leave InstanceT2 and VarT1 implicit
      InstanceC0 := a;
      VarC0 := a;
      // leave InstanceC3 and VarC1 implicit
    }

    static const StaticC0: A
    static const StaticC1: A := StaticC0
    static const StaticC2: A := StaticT0
  }

  datatype Uni = Uni

  method TestStart() {
    Test(Uni);
    Test([Uni]);
  }

  method Test<X(0)>(x: X) {
    var d: Datatype<X> := Dt1(x);
    var c: Class<X> := new Class(x);
    var t: Trait<X> := c;

    print d.InstanceD0, " ++ ";
    print d.InstanceD1, " ++ ";
    print d.InstanceD2, " ++ ";
    print d.InstanceD3, " ++ ";
    print d.InstanceD4, "\n  ** ";
    print Datatype<X>.StaticD0, " ++ ";
    print Datatype<X>.StaticD1, "\n";

    print t.InstanceT0, " ++ ";
    print t.InstanceT1, " ++ ";
    print t.InstanceT2, " ++ ";
    print t.VarT0, " ++ ";
    print t.VarT1, "\n  ** ";
    print Trait<X>.StaticT0, " ++ ";
    print Trait<X>.StaticT1, "\n";

    print c.InstanceT0, " ++ ";
    print c.InstanceT1, " ++ ";
    print c.InstanceT2, " ++ ";
    print c.VarT0, " ++ ";
    print c.VarT1, "\n";
    print c.InstanceC0, " ++ ";
    print c.InstanceC1, " ++ ";
    print c.InstanceC2, " ++ ";
    print c.InstanceC3, "\n  ++ ";
    print c.VarC0, " ++ ";
    print c.VarC1, "\n  ** ";
    print Class<X>.StaticC0, " ++ ";
    print Class<X>.StaticC1, " ++ ";
    print Class<X>.StaticC2, "\n";
  }
}
