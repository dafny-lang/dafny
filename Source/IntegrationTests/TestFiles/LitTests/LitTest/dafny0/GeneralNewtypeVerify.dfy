// RUN: %exits-with 4 %dafny /typeSystemRefresh:1 /generalNewtypes:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module EmptyBool {
  newtype MyBool = bool
  newtype AnyBool = b: bool | true
  newtype NoBool = b: bool | false witness *

  method M0(a: MyBool, b: AnyBool) {
    assert false; // error
  }

  method M1(c: NoBool) {
    assert false;
  }

  method Test() {
    var a: MyBool := true;
    var b: AnyBool := true;
    var c: NoBool := true; // error: not a NoBool
    Recursive(true);
    NonStop(true);
  }

  method Recursive(x: AnyBool) {
    if x {
      Recursive(!x);
    }
  }

  method NonStop(x: AnyBool) {
    NonStop(!x); // error: termination failure
  }
}

module TrueBoolModule {
  newtype TrueBool = b | b witness true

  method M(x: TrueBool) returns (y: TrueBool)
  {
    assert x;
    y := x;
    var z := x && !x ==> x;
    assert z;
  }

  method Test() {
    var b: TrueBool := true;
    var c := M(b);
    var d: bool := c as bool;
    var e := M(2 < 19);
    print b, " ", c, " ", e, "\n"; // true true true
    Recursive(true);
  }

  method Recursive(x: TrueBool)
    decreases x
  {
    var b := x as bool;
    if !b {
      assert false; // we never get here
      Recursive(false);
    }
  }
}
