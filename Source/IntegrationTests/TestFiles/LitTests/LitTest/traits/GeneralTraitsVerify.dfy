// RUN: %exits-with 4 %dafny /typeSystemRefresh:1 /generalTraits:full "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Tests {
  trait Parent { }

  class Class extends Parent { }
  datatype Dt extends Parent = Blue | Red
  codatatype CoDt extends Parent = InfiniteBlue | InfiniteRed
  type Abstract extends Parent
  newtype MyInt extends Parent = int
  newtype MyConstrainedInt extends Parent = x | 0 <= x < 10

  method M(c: Class, d: Dt, co: CoDt, a: Abstract, mi: MyInt, mc: MyConstrainedInt) {
    var p: Parent;
    p := c;
    assert p is Class;
    p := d;
    assert p is Dt;
    p := co;
    assert p is CoDt;
    p := a;
    assert p is Abstract;
    p := mi;
    assert p is MyInt;
    p := mc;
    assert p is MyConstrainedInt;
  }

  method N0(p: Parent) {
    if
    case true =>
      var x: Class;
      x := p as Class; // error
    case true =>
      var x: Dt;
      x := p as Dt; // error
    case true =>
      var x: CoDt;
      x := p as CoDt; // error
    case true =>
      var x: Abstract;
      x := p as Abstract; // error
  }
  
  method N1(p: Parent) {
    if
    case true =>
      var x: MyInt;
      x := p as MyInt; // error
    case true =>
      var x: MyConstrainedInt;
      x := p as MyConstrainedInt; // error
  }

  method P(p: Parent) {
    if
    case p is Class =>
      var x: Class;
      x := p as Class;
    case p is Dt =>
      var x: Dt;
      x := p as Dt;
    case p is CoDt =>
      var x: CoDt;
      x := p as CoDt;
    case p is Abstract =>
      var x: Abstract;
      x := p as Abstract;
    case p is MyInt =>
      var x: MyInt;
      x := p as MyInt;
    case p is MyConstrainedInt =>
      var x: MyConstrainedInt;
      x := p as MyConstrainedInt;
    case true =>
  }

  method Q(c: Class, d: Dt, co: CoDt, a: Abstract, mi: MyInt, mc: MyConstrainedInt) {
    var c: Class, d: Dt, co: CoDt, a: Abstract, mi: MyInt, mc: MyConstrainedInt := c, d, co, a, mi, mc;
    var p: Parent;

    p := c;
    c := p as Class;

    p := d;
    d := p as Dt;

    p := co;
    co := p as CoDt;

    p := a;
    a := p as Abstract;

    p := mi;
    mi := p as MyInt;

    p := mc;
    mc := p as MyConstrainedInt;
  }
}

// ----- test inheritance of instance members

module InstanceMemberInheritance {
  method Test() {
    var p;
    p := TestClass();
    TestParent(p);
    p := TestDatatype();
    TestParent(p);
    p := TestCoDatatype();
    TestParent(p);
    // note, can't call TestAbstract, since it's abstract
    p := TestMyInt();
    TestParent(p);
    p := TestMyConstrainedInt();
    TestParent(p);
  }

  trait Parent {
    const m: nat := 18
    const n: nat
    function F(): int {
      10
    }
    function G(): int
    method M() {
      print "hello M, ";
    }
    method P()
  }

  method TestParent(p: Parent) {
    assert p.m == 18 && p.F() == 10;
    print p.m, " ", p.n, " ", p.F(), " ", p.G(), "\n"; // 18 0 10 <...11>
    p.M(); // hello M,
    p.P(); // hello <...Class>.P
    print "-----\n";
  }

  // ----- class

  class Class extends Parent {
    function G(): int {
      11
    }
    method P() {
      print "hello Class.P\n";
    }
  }

  method TestClass() returns (p: Parent) {
    var x := new Class;
    assert x.m == 18 && x.F() == 10 && x.G() == 11;
    print x.m, " ", x.n, " ", x.F(), " ", x.G(), "\n"; // 18 0 10 11
    x.M(); // hello M,
    x.P(); // hello Class.P
    return x;
  }

  // ----- datatype

  datatype Datatype extends Parent = DtOne
  {
    function G(): int {
      12
    }
    method P() {
      print "hello Dt.P\n";
    }
  }

  method TestDatatype() returns (p: Parent) {
    var x := DtOne;
    assert x.m == 18 && x.F() == 10 && x.G() == 12;
    print x.m, " ", x.n, " ", x.F(), " ", x.G(), "\n"; // 18 0 10 12
    x.M(); // hello M,
    x.P(); // hello Datatype.P
    return x;
  }

  // ----- codatatype

  codatatype CoDatatype extends Parent = CoOne
  {
    function G(): int {
      13
    }
    method P() {
      print "hello CoDatatype.P\n";
    }
  }

  method TestCoDatatype() returns (p: Parent) {
    var x := CoOne;
    assert x.m == 18 && x.F() == 10 && x.G() == 13;
    print x.m, " ", x.n, " ", x.F(), " ", x.G(), "\n"; // 18 0 10 13
    x.M(); // hello M,
    x.P(); // hello CoDatatype.P
    return x;
  }

  // ----- abstract type

  type Abstract extends Parent
  {
    function G(): int {
      14
    }
    method P() {
      print "hello Abstract.P\n";
    }
  }

  method TestAbstract(x: Abstract) returns (p: Parent) {
    assert x.m == 18 && x.F() == 10 && x.G() == 14;
    print x.m, " ", x.n, " ", x.F(), " ", x.G(), "\n"; // 18 0 10 14
    x.M(); // hello M,
    x.P(); // hello Class.P
    return x;
  }

  // ----- newtype without constraint

  newtype MyInt extends Parent = int {
    function G(): int {
      15
    }
    method P() {
      print "hello MyInt.P\n";
    }
  }

  method TestMyInt() returns (p: Parent) {
    var x: MyInt := 100;
    assert x.m == 18 && x.F() == 10 && x.G() == 15;
    print x.m, " ", x.n, " ", x.F(), " ", x.G(), "\n"; // 18 0 10 15
    x.M(); // hello M,
    x.P(); // hello MyInt.P
    return x;
  }

  // ----- newtype with constraint

  newtype MyConstrainedInt extends Parent = x: int | 0 <= x < 10
  {
    function G(): int {
      16
    }
    method P() {
      print "hello MyConstrainedInt.P\n";
    }
  }

  method TestMyConstrainedInt() returns (p: Parent) {
    var x: MyConstrainedInt := 7;
    assert x.m == 18 && x.F() == 10 && x.G() == 16;
    print x.m, " ", x.n, " ", x.F(), " ", x.G(), "\n"; // 18 0 10 16
    x.M(); // hello M,
    x.P(); // hello MyConstrainedInt.P
    return x;
  }
}

module StaticMemberInheritance {
  method Test() {
    var p;
    p := TestClass();
    TestParent(p);
    p := TestDatatype();
    TestParent(p);
    p := TestCoDatatype();
    TestParent(p);
    // note, can't call TestAbstract, since it's abstract
    p := TestMyInt();
    TestParent(p);
    p := TestMyConstrainedInt();
    TestParent(p);
  }

  trait Parent {
    static const m: nat := 18
    static const n: nat
    static function F(): int {
      10
    }
    static method M() {
      print "hello M, ";
    }
  }

  method TestParent(p: Parent) {
    assert p.m == 18 && p.F() == 10;
    print p.m, " ", p.n, " ", p.F(), "\n"; // 18 0 10
    p.M(); // hello M,
    print "-----\n";
  }

  // ----- class

  class Class extends Parent {
  }

  method TestClass() returns (p: Parent) {
    var x := new Class;
    assert x.m == 18 && x.F() == 10;
    print x.m, " ", x.n, " ", x.F(), "\n"; // 18 0 10
    x.M(); // hello M,
    return x;
  }

  // ----- datatype

  datatype Datatype extends Parent = DtOne

  method TestDatatype() returns (p: Parent) {
    var x := DtOne;
    assert x.m == 18 && x.F() == 10;
    print x.m, " ", x.n, " ", x.F(), "\n"; // 18 0 10
    x.M(); // hello M,
    return x;
  }

  // ----- codatatype

  codatatype CoDatatype extends Parent = CoOne

  method TestCoDatatype() returns (p: Parent) {
    var x := CoOne;
    assert x.m == 18 && x.F() == 10;
    print x.m, " ", x.n, " ", x.F(), "\n"; // 18 0 10
    x.M(); // hello M,
    return x;
  }

  // ----- abstract type

  type Abstract extends Parent

  method TestAbstract(x: Abstract) returns (p: Parent) {
    assert x.m == 18 && x.F() == 10;
    print x.m, " ", x.n, " ", x.F(), "\n"; // 18 0 10
    x.M(); // hello M,
    return x;
  }

  // ----- newtype without constraint

  newtype MyInt extends Parent = int

  method TestMyInt() returns (p: Parent) {
    var x: MyInt := 100;
    assert x.m == 18 && x.F() == 10;
    print x.m, " ", x.n, " ", x.F(), "\n"; // 18 0 10
    x.M(); // hello M,
    return x;
  }

  // ----- newtype with constraint

  newtype MyConstrainedInt extends Parent = x: int | 0 <= x < 10

  method TestMyConstrainedInt() returns (p: Parent) {
    var x: MyConstrainedInt := 7;
    assert x.m == 18 && x.F() == 10;
    print x.m, " ", x.n, " ", x.F(),"\n"; // 18 0 10
    x.M(); // hello M,
    return x;
  }
}

module Equality {
  trait GrandParentTrait { }

  trait ParentTrait extends GrandParentTrait { }

  newtype MyInt extends ParentTrait = x | 0 <= x < 100

  method Test() {
    var mi: MyInt := 15;
    var p: ParentTrait := mi;
    var g: GrandParentTrait := mi;

    assert mi is MyInt && p is MyInt && g is MyInt;
    assert mi is ParentTrait && p is ParentTrait && g is ParentTrait;
    assert mi is GrandParentTrait && p is GrandParentTrait && g is GrandParentTrait;

    var w: ParentTrait := g as ParentTrait;
    var x: MyInt := p as MyInt;
    var x': MyInt := g as MyInt;
    var x'': MyInt := mi as MyInt;

    assert x == x' == x'' == x == mi == p == g == w == x;
  }
}

module MoreEquality {

  trait Trait { }
  newtype MyInt extends Trait = x | 0 <= x < 100
  newtype YoInt extends Trait = x | 20 <= x < 25 witness 24

  method Tests() {
    var mi: MyInt := 22;
    var yi: YoInt := 22;

    var a: Trait := mi;
    var b: Trait := yi;

    assert a == mi;
    assert b == yi;
    assert b == mi;
    assert a == yi;
    assert a == b;

    assert a is MyInt;
    assert a is YoInt;
    assert false; // error: the previous two lines should not cause any contradiction
  }
}

module InferredDecreasesClauseForReceiver {
  trait Parent {
    // The following method and function each gets an automatic "decreases a" (without "this")
    method M(a: int) returns (r: int)
    function F(a: int): int
  }

  datatype Unit<X(0)> extends Parent = Unit
  {
    // These overrides had better also omit "this" from "decreases a", or else they won't be pass the override tests
    method M(a: int) returns (r: int) {
      r := a;
    }
    function F(a: int): int {
      a
    }
  }

  type AbstractType<X(0)> extends Parent {
    // These overrides had better also omit "this" from "decreases a", or else they won't be pass the override tests
    method M(a: int) returns (r: int) {
      r := a;
    }
    function F(a: int): int {
      a
    }
  }

  class Class<X(0)> extends Parent {
    // These overrides had better also omit "this" from "decreases a", or else they won't be pass the override tests
    method M(a: int) returns (r: int) {
      r := a;
    }
    function F(a: int): int {
      a
    }
  }

  newtype MyInt extends Parent = int
  {
    // These overrides had better also omit "this" from "decreases a", or else they won't be pass the override tests
    method M(a: int) returns (r: int) {
      r := a;
    }
    function F(a: int): int {
      a
    }
  }
}
