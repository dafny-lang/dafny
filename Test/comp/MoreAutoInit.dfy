// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  Methods.TestStart();
  Functions.TestStart();
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
