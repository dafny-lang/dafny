// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  Methods.TestStart();
  Functions.TestStart();
  Consts.TestStart();
  FunctionsAsValues.TestStart();
  DefaultValuedExpressions.TestStart();
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
    function InstanceN<Bn(0)>(b: Bn): Bn { b }
    static ghost function StaticN<Bn(0)>(b: Bn): Bn { b }
  }

  datatype Datatype<Ad(0)> = Dt0 | Dt1 {
    function InstanceD<Bd(0)>(a: Ad, b: Bd): (Ad, Bd) { (a, b) }
    static ghost function StaticD<Bd(0)>(a: Ad, b: Bd): (Ad, Bd) { (a, b) }
  }

  trait UberTrait<Au(0)> {
    function InstanceU0<Bu(0)>(a: Au, b: Bu): (Au, Bu) { (a, b) }
    function InstanceU1<Bu(0)>(a: Au, b: Bu): (Au, Bu)
    function InstanceU2<Bu(0)>(a: Au, b: Bu): (Au, Bu)
    function InstanceU3<Bu(0)>(a: Au, b: Bu): (Au, Bu)
  }

  trait InBetween<Ai(0)> extends UberTrait<Ai> {
    function InstanceU1<Bi(0)>(a: Ai, b: Bi): (Ai, Bi) { (a, b) }
  }

  trait Trait<At(0)> extends InBetween<At> {
    function InstanceU2<Bt(0)>(a: At, b: Bt): (At, Bt) { (a, b) }
    function InstanceT<Bt(0)>(a: At, b: Bt): (At, Bt)
    function InstanceTBody<Bt(0)>(a: At, b: Bt): (At, Bt) { (a, b) }
    static ghost function StaticT<Bt(0)>(a: At, b: Bt): (At, Bt) { (a, b) }
  }

  class Class<Ac(0)> extends Trait<Ac> {
    function InstanceU3<Bc(0)>(a: Ac, b: Bc): (Ac, Bc) { (a, b) }
    function InstanceT<Bc(0)>(a: Ac, b: Bc): (Ac, Bc) { (a, b) }
    function InstanceC<Bc(0)>(a: Ac, b: Bc): (Ac, Bc) { (a, b) }
    static ghost function StaticC<Bc(0)>(a: Ac, b: Bc): (Ac, Bc) { (a, b) }
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

module FunctionsAsValues {
  trait Trait<G(0), H, J(0)> {
    function Select(g: G, h: H, j: J): G { g }

    function ApplySelect(g: G, h: H, j: J): G {
      var f := Select;
      f(g, h, j)
    }
  }

  class Class extends Trait<int, int, int> {
    constructor () { }
  }

  method TestStart() {
    var c := new Class();
    var x := c.ApplySelect(15, 20, 25);
    print x, "\n";  // 15
  }
}

module DefaultValuedExpressions {
  method TestStart() {
    DoIt<int>();
  }

  // Print the value constructed for x by the caller, and
  // print the supposedly same value constructed via type parameter X.
  method Print<X(0)>(x: X, suffix: string) {
    var y: X;
    print x, "-", y, suffix;
  }

  method DoIt<X(0)>() {
    // primitive types
    var i: int, r: real, b: bool, ch: char, ord: ORDINAL;
    Print(i, " ");
    Print(r, " ");
    Print(b, " ");
    Print(ch, " ");
    print ord, "\n";  // ORDINAL cannot be used as type parameter

    // bitvector types
    var b0: bv0, b1: bv1, b8: bv8, b16: bv16, b32: bv32, b53: bv53, b64: bv64, b100: bv100;
    Print(b0, " ");
    Print(b1, " ");
    Print(b8, " ");
    Print(b16, " ");
    Print(b32, " ");
    Print(b53, " ");
    Print(b64, " ");
    Print(b100, "\n");

    // newtypes
    var nt0: NT0, nt1: NT1, nt2: NT2, nt3: NT3, nt4: NT4, nt5: NT5;
    Print(nt0, " ");
    Print(nt1, " ");
    Print(nt2, " ");
    Print(nt3, " ");
    print nt4, " ";  // NT4 does not currently support (0), so it cannot be used as a type parameter
    print nt5, "\n";  // NT5 does not currently support (0), so it cannot be used as a type parameter

    var nr0: NR0, nr1: NR1;
    Print(nr0, " ");
    print nr1, "\n";  // NR1 does not currently support (0), so it cannot be used as a type parameter

    // possibly-null reference types
    var arr: array?<int>, mat: array3?<int>, c: Class?<int, int>, t: Trait?<int, int>;
    Print(arr, " ");
    Print(mat, " ");
    Print(c, " ");
    Print(t, "\n");

    // non-null reference types
    var Arr: array<int>, Mat: array3<int>;
    print Arr.Length, "\n";  // array<int> does not currently support (0), so it cannot be used as a type parameter
    print Mat.Length0, ":", Mat.Length1, ":", Mat.Length2, "\n";  // array3 does not currently support (0), so it cannot be used as a type parameter

    // type parameter
    var x: X;
    Print(x, "\n");

    // collection types
    var st0: set<int>, st1: iset<int>, ms: multiset<int>, sq: seq<int>, m0: map<int,int>, m1: imap<int,int>;
    Print(st0, " ");
    Print(st1, " ");
    Print(ms, " ");
    Print(sq, " ");
    Print(m0, " ");
    Print(m1, "\n");

    // (co-)datatypes
    var stream: Stream<int>, pstream: PossiblyFiniteStream<int>;
    // print stream, " ", pstream, "\n";  // these types don't currently support initialization
    var color: Color, pc: PossibleCell<Class<int, int>, int>, cell: Cell<int, Class<int, int>>;
    Print(color, " ");
    Print(pc, " ");
    Print(cell, "\n");

    var tup0: (), tup2: (int, real), tup3: (Color, (int, real), ());
    Print(tup0, " ");
    Print(tup2, "\n");
    Print(tup3, "\n");

    // arrow types
    var f0: int ~> int, f1: int --> int;
    Print(f0, " ");  // null
    Print(f1, "\n");  // null

    // subset types
    var s0: S0, s1: S1, s2: S2, s3: S3, s4: S4, s5: S5;
    Print(s0, " ");
    Print(s1, " ");
    Print(s2, " ");
    print s3, " ";  // S3 does not currently support (0), so it cannot be used as a type parameter
    print s4, " ";  // S4 does not currently support (0), so it cannot be used as a type parameter
    print s5, "\n";  // S5 does not currently support (0), so it cannot be used as a type parameter

    var t0: ST0<int, int>, t1: ST1<int, int>, t2: ST2<int, int>, t3: ST3<int, int>;
    Print(t0, " ");
    print t1, " ";  // ST1 does not currently support (0), so it cannot be used as a type parameter
    Print(t2, " ");
    print t3, "\n";  // ST3 does not currently support (0), so it cannot be used as a type parameter
  }

  newtype NT0 = int
  newtype NT1 = x: int | true
  newtype NT2 = x: int | x % 2 == 0
  newtype NT3 = x: int | 0 <= x < 500
  newtype NT4 = x: int | x % 2 == 1 witness 1
  newtype NT5 = x: int | 0 <= x < 500 && x % 2 == 1 witness 1

  newtype NR0 = r: real | 0.0 <= r <= 100.0
  newtype NR1 = r: real | 32.0 <= r <= 212.0 witness 68.0

  class Class<T, U(0)> { }
  class Trait<T, U(0)> { }

  codatatype Stream<T> = More(T, Stream<T>)
  codatatype EmptyOrInfinite<U> = EmptyStream | InfiniteStream(U, Stream<U>)  // regression: this once crashed the Translator
  codatatype PossiblyFiniteStream<T> = Stop | GoOn(T, PossiblyFiniteStream<T>)

  datatype Color = Red | Green | Blue
  datatype PossibleCell<T, U(0)> = Nothing | YesCell(T) | OrThisCell(U)
  datatype Cell<T, U> = LittleCell(T) | BiggerCell(Cell<T, U>)

  type S0 = x: int | true
  type S1 = x: int | 0 <= x < 10
  type S2 = x: S1 | true
  type S3 = x: int | 2 <= x < 10 witness 3
  type S4 = x: S3 | true witness 4
  type S5 = x: S3 | x % 5 == 0 witness 5

  type ST0<T, U(0)> = x: int | x % 5 == 0
  type ST1<T, U(0)> = x: int | x % 5 == 1 witness 11
  type ST2<T, U(0)> = x: int | (if var m: map<T,U> := map[]; m == map[] then 0 else 8) <= x
  type ST3<T, U(0)> = x: int | (if var m: map<T,U> := map[]; m == map[] then 8 else 0) <= x witness 8
}
