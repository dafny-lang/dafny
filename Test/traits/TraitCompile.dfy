// RUN: %dafny /compile:3 /spillTargetCode:3 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait TT
{
  function method Plus(x:int, y:int) : int
    requires x > y
  {
     x + y
  }
  function method Times(x:int, y:int) : int
    requires x > y
  static function method StaticMinus(x:int, y:int) : int
    requires x > y
  {
     x - y
  }

  method Double(x: int)
  {
    print "d=", x+x, "\n";
  }
  method AddFive(x: int)
  static method StaticTriple(x: int)
  {
    print "t=", 3*x, "\n";
  }
}

class CC extends TT
{
  function method Times(x:int, y:int) : int
    requires x>y
  {
    x * y
  }
  method AddFive(x: int)
  {
    print "a5=", x+5, "\n";
  }
}

method Client(t: TT)
{
  var x := t.Plus(10, 2);
  print "x=", x, "\n";
  t.Double(400);
  t.AddFive(402);
  t.StaticTriple(404);
}

method Main()
{
  var c := new CC;
  var y := c.Plus(100, 20);
  print "y=", y, "\n";
  Client(c);
  var z := TT.StaticMinus(50, 20);
  print "z=", z, "\n";
  var z' := CC.StaticMinus(50, 20);
  print "z'=", z', "\n";
  var w := c.StaticMinus(50, 20);
  print "w=", w, "\n";

  c.Double(500);
  { var cc: CC := new CC; cc.AddFive(502); }
  c.StaticTriple(504);
  TT.StaticTriple(504);
  CC.StaticTriple(505);

  var seven := OtherModule.Y.F(15);
  assert seven == 7;
  var b := OtherModule.Y.P(seven as real);
  print "From OtherModule.Y: ", seven, " and ", b, "\n";
  seven := OtherModule.X.F(15);
  assert seven == 7;
  b := OtherModule.X.P(seven as real);
  print "From OtherModule.X: ", seven, " and ", b, "\n";

  TestFields.Test();

  GenericBasics.Test();
  Generics.Test();

  TraitsExtendingTraits.Test();
}

module OtherModule {
  trait Y {
    static function method F(x: int): int
    { x / 2 }
    static method P(t: real) returns (f: bool)
    {
      print "This is OtherModule.P(", t, ")\n";
      f := t < 10.0;
    }
  }
  class X extends Y {
  }
}


module TestFields {
  trait J {
    var f: int
  }

  class C extends J {
  }

  method Test() {
    var c := new C;
    var j: J := c;

    c.f := 15;
    assert j.f == 15;
    print "c.f= ", c.f, " j.f= ", j.f, "\n";
    j.f := 18;
    assert c.f == 18;
    print "c.f= ", c.f, " j.f= ", j.f, "\n";
  }
}

module GenericBasics {
  // To compile these correctly requires that certain type-parameter renamings be done.

  trait Tr<A, B(0)> {
    var xyz: B
    const abc: B
    static const def: B

    method Inst(x: int, a: A, b: B) returns (bb: B) { bb := b; }
    static method Stat(y: int, a: A, b: B) returns (bb: B) { bb := b; }

    function method Teen<R>(a: (A, R)): B
    static function method STeen<R>(a: (A, R), b: B): B { b }

    // here are some functions with/without a named result value, which is treated separately in the verifier; these tests check on box/unbox-ing in the verifier
    function method RValue0<X>(x: X): B
    function method RValue1<X>(x: X): (r: B)
    function method RValue2<X>(x: X): B
    function method RValue3<X>(x: X): (r: B)

    method ReferToTraitMembers(a: A, b: B, tt: Tr<bool, real>)
      modifies this
    {
      xyz := b;
      this.xyz := b;
      var x := xyz;
      var y := this.xyz;

      var bb := Inst(0, a, b);
      bb := this.Inst(0, a, b);
      var rr := tt.Inst(0, true, 5.0);

      bb := Stat(1, a, b);
      bb := this.Stat(1, a, b);
      rr := tt.Stat(1, true, 5.0);
      bb := Tr.Stat(1, a, b);
      var ss := Tr.Stat(2, [2], {2});  // calls method in Tr<seq<int>, set<int>>

      bb := Teen<bv7>((a, 70));
      bb := this.Teen<bv7>((a, 70));
      rr := tt.Teen<bv7>((false, 70));

      bb := STeen<bv7>((a, 70), b);
      bb := this.STeen<bv7>((a, 70), b);
      rr := tt.STeen<bv7>((false, 70), 0.71);
      bb := Tr.STeen<bv7>((false, 70), b);
      ss := Tr<seq<int>, set<int>>.STeen<bv7>(([], 70), {80});
    }
  }

  // Cl has fewer type parameters than Tr
  class Cl<Q> extends Tr<Q, int> {
    constructor () {
      abc := 100;
      this.abc := 101;
      xyz := 20;
      this.xyz := 21;
      new;
      xyz := 22;
      this.xyz := 23;
    }
    method ReferToMembers(a: Q, b: int)
      modifies this
    {
      xyz := b;
      this.xyz := b;
      var x := xyz;
      var y := this.xyz;

      var tt: Tr<Q, int> := this;

      var bb := Inst(0, a, b);
      bb := this.Inst(0, a, b);
      bb := tt.Inst(0, a, b);

      bb := Stat(1, a, b);
      bb := this.Stat(1, a, b);
      bb := tt.Stat(1, a, b);
      bb := Tr.Stat(1, a, b);
      var ss := Tr.Stat(2, [2], {2});  // calls method in Tr<seq<int>, set<int>>

      bb := Teen<bv7>((a, 70));
      bb := this.Teen<bv7>((a, 70));
      var rr := tt.Teen<bv7>((a, 70));

      bb := STeen<bv7>((a, 70), b);
      bb := this.STeen<bv7>((a, 70), b);
      rr := tt.STeen<bv7>((a, 70), 71);
      bb := Tr.STeen<bv7>((false, 70), b);
      ss := Tr<seq<int>, set<int>>.STeen<bv7>(([], 70), {80});
    }

    function method Teen<S>(a: (Q, S)): int { 12 }

    function method RValue0<XX>(x: XX): int { 5 }
    function method RValue1<XX>(x: XX): int { 5 }
    function method RValue2<XX>(x: XX): (r: int) { 5 }
    function method RValue3<XX>(x: XX): (r: int) { 5 }
  }


  // Mega has more type parameters than Tr
  class Mega<P, Q, L> extends Tr<Q, int> {
    constructor () {
      abc := 100;
      this.abc := 101;
      xyz := 20;
      this.xyz := 21;
      new;
      xyz := 22;
      this.xyz := 23;
    }
    method ReferToMembers(a: Q, b: int)
      modifies this
    {
      xyz := b;
      this.xyz := b;
      var x := xyz;
      var y := this.xyz;

      var tt: Tr<Q, int> := this;

      var bb := Inst(0, a, b);
      bb := this.Inst(0, a, b);
      bb := tt.Inst(0, a, b);

      bb := Stat(1, a, b);
      bb := this.Stat(1, a, b);
      bb := tt.Stat(1, a, b);
      bb := Tr.Stat(1, a, b);
      var ss := Tr.Stat(2, [2], {2});  // calls method in Tr<seq<int>, set<int>>

      bb := Teen<bv7>((a, 70));
      bb := this.Teen<bv7>((a, 70));
      var rr := tt.Teen<bv7>((a, 70));

      bb := STeen<bv7>((a, 70), b);
      bb := this.STeen<bv7>((a, 70), b);
      rr := tt.STeen<bv7>((a, 70), 71);
      bb := Tr.STeen<bv7>((false, 70), b);
      ss := Tr<seq<int>, set<int>>.STeen<bv7>(([], 70), {80});
    }

    function method Teen<S>(a: (Q, S)): int { 12 }

    function method RValue0<XX>(x: XX): int { 5 }
    function method RValue1<XX>(x: XX): int { 5 }
    function method RValue2<XX>(x: XX): (r: int) { 5 }
    function method RValue3<XX>(x: XX): (r: int) { 5 }
  }

  method Test() {
    var c: Cl<real> := new Cl();
    var m: Mega<bool, real, Cl<real>> := new Mega();
    // not all compile targets support seq<TRAIT> yet; therefore, we code around it, to at least get calls via "t: Tr"
    ghost var ts: seq<Tr<real, int>> := [c, m];
    var t: Tr;
    var i := 0;
    while i < 2
      invariant 0 <= i <= 2
    {
      t := if i == 0 then c else m;
      assert t == ts[i];
      print t.xyz, " ";
      print t.abc, " ";
      print t.def, " ";
      var bb := t.Inst(50, 51.0, 52);
      print bb, " ";
      bb := t.Stat(50, 51.0, 52);
      print bb, " ";
      print t.Teen<bv9>((0.5, 100)), " ";
      print t.STeen<bv9>((0.5, 100), 53), " ";
      print t.RValue0<(bv2,bv3)>((3, 3)), " ";
      print t.RValue1<(bv2,bv3)>((3, 3)), " ";
      print t.RValue2<(bv2,bv3)>((3, 3)), " ";
      print t.RValue3<(bv2,bv3)>((3, 3)), "\n";
      i := i + 1;
    }
  }
}

module Generics {
  trait Identity {
    method Call<T>(x: T) returns (r: T)
  }

  class IdentityImpl extends Identity {
    method Call<T>(x: T) returns (r: T) {
      r := x;
    }
  }

  // TODO-RS: Call this something else: Closure? Method?
  trait Function<T, R> {
    method Call(t: T) returns (r: R) decreases *
    method Compose<S>(f: Function<S, T>) returns (res: Function<S, R>) {
      res := new ComposedFunction(f, this);
    }
  }

  type IntFunction<T> = Function<T, int>

  class ComposedFunction<S, T, RR> extends Function<S, RR> {
    const first: Function<S, T>
    const second: Function<T, RR>

    constructor(first: Function<S, T>, second: Function<T, RR>) {
      this.first := first;
      this.second := second;
    }

    method Call(s: S) returns (r: RR) decreases * {
      var t := first.Call(s);
      r := second.Call(t);
    }
  }

  class Triple extends Function<int, int> {
    constructor() {}
    method Call(t: int) returns (r: int) {
      r := 3*t;
    }
  }

  method Test() {
    var tripler := new Triple();
    var x := tripler.Call(42);
    print "x=", x, "\n";
  }
}

module TraitsExtendingTraits {
  type Odd = x | x % 2 == 1 witness 9

  /*
   A     B  C
   |    /\ / \
   K   M  N  |
    \ /  /  /
     \  /  /
      \ | /
        G
   */

  trait A<Y0, Y1> {
    var y0: Y0
    const y1: Y1
    method SetY(y: Y0)
      modifies this
    {
      y0 := y;
    }
    function method GetY(): Y0
      reads this
    {
      y0
    }
    function method GetY'(): Y0
      reads this
  }
  trait B {
    var b: bool
    method Quantity() returns (x: int)
    method Twice() returns (x: int)
  }
  trait C {
  }

  trait K<Y> extends A<Y, Odd> {
    const k := y1
    function method GetY'(): Y
      reads this
    {
      y0
    }
  }

  trait M extends B {
    method Quantity() returns (x: int)
      ensures 0 <= x <= 20
    {
      return 15;
    }
  }
  trait N extends B, C {
    method Twice() returns (x: int) {
      x := Quantity();
      x := 2 * x;
    }
  }

  class G<X> extends K<X>, K<X>, M, N, C {
    constructor (x: X) {
      y0 := x;
    }
  }

  method Test() {
    var g := new G<real>(5.2);
    print g.y0, " ", g.y1, " ", g.b, "\n";  // 5.2 9 false
    var m: M := g;
    var n: N := g;
    m.b := true;
    print g.b, " ", m.b, " ", n.b, "\n";  // true true true
    print g.GetY(), " ", g.GetY'(), "\n"; // 5.2 5.2
    g.SetY(1.2);
    print g.GetY(), " ", g.GetY'(), "\n";  // 1.2 1.2

    var q := g.Quantity();
    assert 0 <= q <= 20;
    var qq := g.Twice();
    print q, " ", qq, "\n";  // 15 30
    q := m.Quantity();
    assert 0 <= q <= 20;
    qq := m.Twice();
    print q, " ", qq, "\n";  // 15 30
    q := n.Quantity();
    qq := n.Twice();
    print q, " ", qq, "\n";  // 15 30
  }
}
