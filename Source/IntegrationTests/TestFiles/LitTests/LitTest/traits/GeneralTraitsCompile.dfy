// RUN: %testDafnyForEachCompiler "%s" --refresh-exit-code=0 -- --general-traits:full --type-system-refresh

method Main() {
  Tests.Test();
  InstanceMemberInheritance.Test();
  StaticMemberInheritanceAccessViaName.Test();
  StaticMemberInheritanceAccessViaReceiver.Test();
  NiceStarterTests.Test();
  print "done\n";
}

module Tests {
  method Test() {
    var c: Class := new Class;
    var d: Dt := Blue;
    var co: CoDt := InfiniteBlue;
    var mi: MyInt := 65;
    var mc: MyConstrainedInt := 6;

    M(c, d, co, mi, mc);
    P(c);
    P(d);
    P(co);
    P(mi);
    P(mc);
    Q(c, d, co, mi, mc);
  }

  trait Parent { }

  class Class extends Parent { }
  datatype Dt extends Parent = Blue | Red
  codatatype CoDt extends Parent = InfiniteBlue | InfiniteRed
  newtype MyInt extends Parent = int
  newtype MyConstrainedInt extends Parent = x | 0 <= x < 10

  method M(c: Class, d: Dt, co: CoDt, mi: MyInt, mc: MyConstrainedInt) {
    var p: Parent;
    p := c;
    assert p is Class;
    p := d;
    assert p is Dt;
    p := co;
    assert p is CoDt;
    p := mi;
    assert p is MyInt;
    p := mc;
    assert p is MyConstrainedInt;
  }

  method P(p: Parent)
    requires p is Class || p is Dt || p is CoDt || p is MyInt || p is MyConstrainedInt
  {
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
    case p is MyInt =>
      var x: MyInt;
      x := p as MyInt;
    case p is MyConstrainedInt =>
      var x: MyConstrainedInt;
      x := p as MyConstrainedInt;
  }

  method Q(c: Class, d: Dt, co: CoDt, mi: MyInt, mc: MyConstrainedInt) {
    var c: Class, d: Dt, co: CoDt, mi: MyInt, mc: MyConstrainedInt := c, d, co, mi, mc;
    var p: Parent;

    p := c;
    c := p as Class;

    p := d;
    d := p as Dt;

    p := co;
    co := p as CoDt;

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

module StaticMemberInheritanceAccessViaName {
  method Test() {
    TestParent();
    TestClass();
    TestDatatype();
    TestCoDatatype();
    TestMyInt();
    TestMyConstrainedInt();
    print "=====\n";
  }

  trait Parent {
    static const m: nat := 18
    static const n: nat
    static function F(): int {
      10
    }
    static method M() {
      print "hello static-via-name M\n";
    }
  }

  method TestParent() {
    assert Parent.m == 18 && Parent.F() == 10;
    print Parent.m, " ", Parent.n, " ", Parent.F(), "\n"; // 18 0 10
    Parent.M(); // hello static-via-name M
    print "-----\n";
  }

  // ----- class

  class Class extends Parent {
  }

  method TestClass() {
    assert Class.m == 18 && Class.F() == 10;
    print Class.m, " ", Class.n, " ", Class.F(), "\n"; // 18 0 10
    Class.M(); // hello static-via-name M
  }

  // ----- datatype

  datatype Datatype extends Parent = DtOne

  method TestDatatype() {
    assert Datatype.m == 18 && Datatype.F() == 10;
    print Datatype.m, " ", Datatype.n, " ", Datatype.F(), "\n"; // 18 0 10
    Datatype.M(); // hello static-via-name M
  }

  // ----- codatatype

  codatatype CoDatatype extends Parent = CoOne

  method TestCoDatatype() {
    assert CoDatatype.m == 18 && CoDatatype.F() == 10;
    print CoDatatype.m, " ", CoDatatype.n, " ", CoDatatype.F(), "\n"; // 18 0 10
    CoDatatype.M(); // hello static-via-name M
  }

  // ----- newtype without constraint

  newtype MyInt extends Parent = int

  method TestMyInt() {
    assert MyInt.m == 18 && MyInt.F() == 10;
    print MyInt.m, " ", MyInt.n, " ", MyInt.F(), "\n"; // 18 0 10
    MyInt.M(); // hello static-via-name M
  }

  // ----- newtype with constraint

  newtype MyConstrainedInt extends Parent = x: int | 0 <= x < 10

  method TestMyConstrainedInt() {
    assert MyConstrainedInt.m == 18 && MyConstrainedInt.F() == 10;
    print MyConstrainedInt.m, " ", MyConstrainedInt.n, " ", MyConstrainedInt.F(),"\n"; // 18 0 10
    MyConstrainedInt.M(); // hello static-via-name M
  }
}

module StaticMemberInheritanceAccessViaReceiver {
  method Test() {
    var p;
    p := TestClass();
    TestParent(p);
    p := TestDatatype();
    TestParent(p);
    p := TestCoDatatype();
    TestParent(p);
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
      print "hello static-via-receiver M\n";
    }
  }

  method TestParent(p: Parent) {
    assert p.m == 18 && p.F() == 10;
    print p.m, " ", p.n, " ", p.F(), "\n"; // 18 0 10
    p.M(); // hello static-via-receiver M
    print "-----\n";
  }

  // ----- class

  class Class extends Parent {
  }

  method TestClass() returns (p: Parent) {
    var x := new Class;
    assert x.m == 18 && x.F() == 10;
    print x.m, " ", x.n, " ", x.F(), "\n"; // 18 0 10
    x.M(); // hello static-via-receiver M
    return x;
  }

  // ----- datatype

  datatype Datatype extends Parent = DtOne

  method TestDatatype() returns (p: Parent) {
    var x := DtOne;
    assert x.m == 18 && x.F() == 10;
    print x.m, " ", x.n, " ", x.F(), "\n"; // 18 0 10
    x.M(); // hello static-via-receiver M
    return x;
  }

  // ----- codatatype

  codatatype CoDatatype extends Parent = CoOne

  method TestCoDatatype() returns (p: Parent) {
    var x := CoOne;
    assert x.m == 18 && x.F() == 10;
    print x.m, " ", x.n, " ", x.F(), "\n"; // 18 0 10
    x.M(); // hello static-via-receiver M
    return x;
  }

  // ----- newtype without constraint

  newtype MyInt extends Parent = int

  method TestMyInt() returns (p: Parent) {
    var x: MyInt := 100;
    assert x.m == 18 && x.F() == 10;
    print x.m, " ", x.n, " ", x.F(), "\n"; // 18 0 10
    x.M(); // hello static-via-receiver M
    return x;
  }

  // ----- newtype with constraint

  newtype MyConstrainedInt extends Parent = x: int | 0 <= x < 10

  method TestMyConstrainedInt() returns (p: Parent) {
    var x: MyConstrainedInt := 7;
    assert x.m == 18 && x.F() == 10;
    print x.m, " ", x.n, " ", x.F(),"\n"; // 18 0 10
    x.M(); // hello static-via-receiver M
    return x;
  }
}

module NiceStarterTests {
  trait Parent {
    method MyMethod<Y(0)>(a: int) returns (r: int)
  }

  datatype Color<X(0)> extends Parent = Blue | Gray(n: nat)
  {
    method MyMethod<Y(0)>(a: int) returns (r: int) {
      var x: X;
      var y: Y;
      r := a + a + 3;
    }
  }

  class MyClass<X(0)> extends Parent
  {
    method MyMethod<Y(0)>(a: int) returns (r: int) {
      var x: X;
      var y: Y;
      r := a + 3;
    }
  }

  method Test() {
    var u := Color<real>.Gray(15);
    var s := u.MyMethod<bool>(10);

    var p: Parent := u;
    var t := p.MyMethod<bool>(10);
    print s, " ", t, "\n"; // 23 23
  }
}
