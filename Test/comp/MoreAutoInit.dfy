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
    method InstanceN<Bn(0)>(b: Bn) returns (bb: Bn) { }
    static method StaticN<Bn(0)>(b: Bn) returns (bb: Bn) { }
  }

  datatype Datatype<Ad(0)> = Dt0 | Dt1 {
    method InstanceD<Bd(0)>(a: Ad, b: Bd) returns (aa: Ad, bb: Bd) { }
    static method StaticD<Bd(0)>(a: Ad, b: Bd) returns (aa: Ad, bb: Bd) { }
  }

  trait UberTrait<Au(0)> {
    method InstanceU0<Bu(0)>(a: Au, b: Bu) returns (aa: Au, bb: Bu) { }
    method InstanceU1<Bu(0)>(a: Au, b: Bu) returns (aa: Au, bb: Bu)
    method InstanceU2<Bu(0)>(a: Au, b: Bu) returns (aa: Au, bb: Bu)
    method InstanceU3<Bu(0)>(a: Au, b: Bu) returns (aa: Au, bb: Bu)
  }

  trait InBetween<Ai(0)> extends UberTrait<Ai> {
    method InstanceU1<Bi(0)>(a: Ai, b: Bi) returns (aa: Ai, bb: Bi) { }
  }

  trait Trait<At(0)> extends InBetween<At> {
    method InstanceU2<Bt(0)>(a: At, b: Bt) returns (aa: At, bb: Bt) { }
    method InstanceT<Bt(0)>(a: At, b: Bt) returns (aa: At, bb: Bt)
    method InstanceTBody<Bt(0)>(a: At, b: Bt) returns (aa: At, bb: Bt) { }
    static method StaticT<Bt(0)>(a: At, b: Bt) returns (aa: At, bb: Bt) { }
  }

  class Class<Ac(0)> extends Trait<Ac> {
    method InstanceU3<Bc(0)>(a: Ac, b: Bc) returns (aa: Ac, bb: Bc) { }
    method InstanceT<Bc(0)>(a: Ac, b: Bc) returns (aa: Ac, bb: Bc) { }
    method InstanceC<Bc(0)>(a: Ac, b: Bc) returns (aa: Ac, bb: Bc) { }
    static method StaticC<Bc(0)>(a: Ac, b: Bc) returns (aa: Ac, bb: Bc) { }
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
    function method InstanceN<Bn(0)>(b: Bn): Bn { b }
    static function method StaticN<Bn(0)>(b: Bn): Bn { b }
  }

  datatype Datatype<Ad(0)> = Dt0 | Dt1 {
    function method InstanceD<Bd(0)>(a: Ad, b: Bd): (Ad, Bd) { (a, b) }
    static function method StaticD<Bd(0)>(a: Ad, b: Bd): (Ad, Bd) { (a, b) }
  }

  trait UberTrait<Au(0)> {
    function method InstanceU0<Bu(0)>(a: Au, b: Bu): (Au, Bu) { (a, b) }
    function method InstanceU1<Bu(0)>(a: Au, b: Bu): (Au, Bu)
    function method InstanceU2<Bu(0)>(a: Au, b: Bu): (Au, Bu)
    function method InstanceU3<Bu(0)>(a: Au, b: Bu): (Au, Bu)
  }

  trait InBetween<Ai(0)> extends UberTrait<Ai> {
    function method InstanceU1<Bi(0)>(a: Ai, b: Bi): (Ai, Bi) { (a, b) }
  }

  trait Trait<At(0)> extends InBetween<At> {
    function method InstanceU2<Bt(0)>(a: At, b: Bt): (At, Bt) { (a, b) }
    function method InstanceT<Bt(0)>(a: At, b: Bt): (At, Bt)
    function method InstanceTBody<Bt(0)>(a: At, b: Bt): (At, Bt) { (a, b) }
    static function method StaticT<Bt(0)>(a: At, b: Bt): (At, Bt) { (a, b) }
  }

  class Class<Ac(0)> extends Trait<Ac> {
    function method InstanceU3<Bc(0)>(a: Ac, b: Bc): (Ac, Bc) { (a, b) }
    function method InstanceT<Bc(0)>(a: Ac, b: Bc): (Ac, Bc) { (a, b) }
    function method InstanceC<Bc(0)>(a: Ac, b: Bc): (Ac, Bc) { (a, b) }
    static function method StaticC<Bc(0)>(a: Ac, b: Bc): (Ac, Bc) { (a, b) }
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
  datatype Datatype<Ad(0)> = Dt0(a: Ad) | Dt1(a: Ad) {
    const InstanceD0: Ad
    const InstanceD1: Ad := InstanceD0
    const InstanceD2: Ad := InstanceD3
    const InstanceD3: Ad := a
    const InstanceD4: Ad := InstanceD3
    static const StaticD0: Ad
    static const StaticD1: Ad := StaticD0
  }

  trait Trait<At(0)> {
    const InstanceT0: At
    const InstanceT1: At := InstanceT0
    const InstanceT2: At
    var VarT0: At
    var VarT1: At
    static const StaticT0: At
    static const StaticT1: At := StaticT0
  }

  class Class<Ac(0)> extends Trait<Ac> {
    const InstanceC0: Ac
    const InstanceC1: Ac := InstanceC0
    const InstanceC2: Ac := InstanceT0
    const InstanceC3: Ac
    var VarC0: Ac
    var VarC1: Ac
    constructor (a: Ac) {
      InstanceT0 := a;
      VarT0 := a;
      // leave InstanceT2 and VarT1 implicit
      InstanceC0 := a;
      VarC0 := a;
      // leave InstanceC3 and VarC1 implicit
    }

    static const StaticC0: Ac
    static const StaticC1: Ac := StaticC0
    static const StaticC2: Ac := StaticT0
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
