// RUN: %dafny /compile:3  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const one:int := 1
const two:int := one * 2
const three:int := one + two
const Pi:real := 3.14

class Calendar {
  static const months:int := 12
  static const weeks:int := 52
}

method Main() {
  print "one := ", one, "\n";
  print "two := ", two, "\n";
  print "three := ", three, "\n";
  assert three == 3;
  print "Pi := ", Pi, "\n";
  assert Pi == 3.14;
  var weeks := Calendar.weeks;
  print "months := ", Calendar.months, "\n";
  print "weeks := ", weeks, "\n";
  assert weeks == 52;

  var c := new C;
  var tu := c.M();  // 11
  print tu, " ";
  print c.G(c), " ";  // 16
  print c.H(c), " ";  // 173
  print C.x, " ";  // 6
  var g := new Generic<real>;
  var putItHere := g.y;
  print putItHere, " ";  // 63
  var go := g.M();
  print go, "\n";  // 63

  var noRhs := new NoRHS;
  print "noRhs.y = ", noRhs.y, "\n";

  var cl := new Class;
  cl.Test();
  var ii := new InstanceInit(13);
  print ii.x0, " ", ii.x1, " ", ii.y2, " ", ii.y3, " ", ii.r, "\n";  // 93, 7, 89, 12, 8.54

  print mmgg, " ", UninterpretedStaticsTrait.mmtt, " ", UninterpretedStaticsClass.mmcc, "\n";

  InitializationDependencies.PrintEm();
}

class C {
  static const x: int := y+1
  static const y: int := 5
  var z: int
  static function G(c: C): int
    ensures G(c) == 16
  {
    x + y + c.y
  }

  const a: int := b+2
  const b: int := 50
  function H(c: C): int
    ensures H(c) == 50 + 52 + 50 + 6 + 5 + 5 + 5 == 173
  {
    a + b + c.b + x + y + c.y + C.y
  }

  method M() returns (r: int)
    ensures r == 11
  {
    r := x + y;
  }
}

class Generic<G> {
  const y: int := 63
  method M() returns (q: int)
    ensures q == 63
  {
    q := this.y;
  }
}

newtype Six = x | 6 <= x witness 6

class NoRHS {
  const y: Six
}

// ---------- traits --------------------

trait Trait {
  const x0: Six
  const x1: Six := 7

  static const y: Six := 7
}

class Class extends Trait {
  method Test() {
    assert x1 == 7 && y == 7;
    print x0, " ", x1, " ", y, "\n";
  }
}

method MMethod(tr: Trait?) {
  assert Trait.y == 7;
  assert tr.y == 7;
  assert tr == null || tr.x1 == 7;
}

// ---------- instanced-based initialization --------

class InstanceInit extends Trait {
  const y2: Six
  const y3: Six := 12
  const N: int := 20

  var r: real

  constructor (u: Six)
    requires 10 <= u
  {
    x0 := 80 + u;
    var arr := new real[N];
    arr[8] := 2.7;
    r := arr[8];
    y2 := 77 + y3;
    new;
    assert x0 == u + 80 && x1 ==7;
    assert y2 == 89 && y3 == 12;
    assert arr.Length == 20;
    arr[9] := 3.14;
    r := r + arr[8] + arr[9];  // 8.54
  }
}

// ---------- class- and module-level const's without RHS --------

const mmgg: Six

trait UninterpretedStaticsTrait {
  static const mmtt: Six
}

class UninterpretedStaticsClass extends UninterpretedStaticsTrait {
  static const mmcc: Six
}

// ---------- test type/allocation axiom of const fields --------

type byte = x | 0 <= x < 256

class MyClass {
  const B: array<byte>

  method M()
  {
    var x: array?<byte> := B;
    var y: array<byte> := x;  // this line generates a proof obligation, but it should pass
  }
}

// ---------- static const fields in a generic class have its own axioms --------

class MyOnePurposeClass {
  static const z: int
  static const w: int := 76
  static const self: MyOnePurposeClass?
}

class MyGenericClass<X(00), Y(00)> {
  ghost static const x: X
  ghost static const y: Y
  static const z: int
  static const w: int := 76
  static const self: MyGenericClass?<X,Y>
  static const almostSelf: MyGenericClass?<Y,X>
  static const another: MyGenericClass?<byte,seq<X>>
}

// ---------- initialization dependencies --------

module InitializationDependencies {
  class C {
    static const a: int := b
    static const b: int := D.m
    static const c: int := b
  }

  class D {
    static const m: int := 20
  }

  class R {
    const a: int := b + b
    const b: int := this.m
    const c: int := b

    const m: int := 21

    const n: int := F(b)
    function F(nn: int): int {
      2 * nn + C.b
    }
  }

  method PrintEm()
  {
    print C.a, " ";
    print C.b, " ";
    print C.c, "\n";
    print D.m, "\n";
    var r := new R;
    print r.a, " ";
    print r.b, " ";
    print r.c, " ";
    print r.m, "\n";
    print r.n, "\n";
  }
}

module A {
  const x: int := 100
}
module B refines A {
  ghost const x: int
  lemma TestRhsIsInherited() {
    assert x == 100;
  }
}
