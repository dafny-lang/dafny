// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment --type-system-refresh --general-newtypes

method Main() {
  Numerics.Test();
  SimpleBoolAndint.Test();
  TrivialConstraint.Test();
}

module Numerics {
  newtype i32 = x: int | -0x8000_0000 <= x < 0x8000_0000

  newtype j32 = i32

  newtype k32 = j: j32 | true

  newtype nn = x: int | 0 <= x
  newtype byte = n: nn | n < 256

  method Test() {
    var i: i32 := 100;
    var j: j32 := 100;

    print i, " ", j, "\n"; // 100 100
    print i == i, " ", j == j, "\n"; // true true
    print i == j as i32, " ", i as j32 == j, "\n"; // true true
    print i as int == j as int, "\n"; // true

    var k: k32 := 99;
    var n: nn := 99;
    var b: byte := 99;

    print k, " ", n, " ", b, "\n"; // 99 99
    print k == k, " ", n == n, " ", b == b, "\n"; // true true true
    print k == n as k32, " ", n == b as nn, " ", b == k as byte, "\n"; // true true true
  }
}

module SimpleBoolAndint {
  export
    provides Test

  newtype MyBool = bool
  newtype MyInt = int

  method M(x: MyBool) returns (y: MyBool)
  {
    y := x;
    var z := x && !x ==> x;
    assert z;
  }

  method Test() {
    var b: MyBool := true;
    var c := M(b);
    var d: bool := c as bool;
    var e := M((2 < 19 < 17 < 19 <==> true as bool) as MyBool);
    var f := M((2 < 19 < 17 < 19 <==> true) as MyBool);
    var g := M(2 < 19 < 17 < 19);
    print b, " ", c, " ", e, " ", f, " ", g, "\n"; // true true false false false
    TestMore();
    Operators(true);
  }

  method TestMore() {
    var b: bool;
    var c: MyBool;
    c := b as MyBool;
    b := c as bool;

    var x: int;
    var y: MyInt;
    y := x as MyInt;
    x := y as int;

    print b, " ", c, " ", x, " ", y, "\n"; // false false 0 0

    b := x as MyInt == y;
    c := x == y as int;
    print b, " ", c, "\n"; // true true

    b := x as MyInt < y;
    c := x < y as int;
    print b, " ", c, "\n"; // false false
  }

  method Operators(b: MyBool) {
    print b == b && !(b != b) && (b <==> b) && (b ==> b) && (!b ==> b) && (b <== b) && (b <== !b) && (b && b) && (b || b), "\n"; // true
  }
}

module TrivialConstraint {
  export
    provides Test

  newtype MyBool = b: bool | true
  newtype MyInt = int

  method M(x: MyBool) returns (y: MyBool)
  {
    y := x;
    var z := x && !x ==> x;
    assert z;
  }

  method Test() {
    var b: MyBool := true;
    var c := M(b);
    var d: bool := c as bool;
    var e := M((2 < 19 < 17 < 19 <==> true as bool) as MyBool);
    var f := M((2 < 19 < 17 < 19 <==> true) as MyBool);
    var g := M(2 < 19 < 17 < 19);
    print b, " ", c, " ", e, " ", f, " ", g, "\n"; // true true false false false
    TestMore();
    Operators(true);
  }

  method TestMore() {
    var b: bool;
    var c: MyBool;
    c := b as MyBool;
    b := c as bool;

    var x: int;
    var y: MyInt;
    y := x as MyInt;
    x := y as int;

    print b, " ", c, " ", x, " ", y, "\n"; // false false 0 0

    b := x as MyInt == y;
    c := x == y as int;
    print b, " ", c, "\n"; // true true

    b := x as MyInt < y;
    c := x < y as int;
    print b, " ", c, "\n"; // false false
  }

  method Operators(b: MyBool) {
    print b == b && !(b != b) && (b <==> b) && (b ==> b) && (!b ==> b) && (b <== b) && (b <== !b) && (b && b) && (b || b), "\n"; // true
  }
}
