// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment --type-system-refresh --general-newtypes

method Main() {
  SimpleBoolAndint.Test();
  TrivialConstraint.Test();
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
