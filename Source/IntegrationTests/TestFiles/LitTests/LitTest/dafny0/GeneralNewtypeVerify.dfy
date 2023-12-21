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

  method Stops(x: AnyBool) {
    if x {
      Stops(!x);
    }
  }

  method AllCases(m: MyBool, a: AnyBool) {
    if
    case !m && !a as MyBool =>
    case !m as AnyBool && a =>
    case m as bool && !a as bool as AnyBool as bool =>
    case m as bool as AnyBool && a =>
  }
}

module TrueBoolModule {
  newtype TrueBool = b | b witness true

  method M(x: TrueBool) returns (y: TrueBool)
  {
    assert x;
    y := x;
    var z := x ==> x;
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

  method Literals() {
    var x: TrueBool;
    x := true;
    x := false; // error: false is not a TrueBool
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

  method IntermediateExpressions0(x: TrueBool) {
    while x {
      break;
    }
    while {
      case false =>
      case x => break;
      case true => break;
    }

    if
    case true =>
      var u := x && !x; // error: !x is not a TrueBool
    case x =>
      var u := (!(x as bool) || x as bool) as TrueBool;
  }

  newtype FalseBool = b | !b

  method IntermediateExpressions1(x: TrueBool, y: FalseBool) {
    if * {
      var _ := true && (x <==> x);
    } else if * {
      var _ := false || (y <==> y); // error: (y <==> y) is not a FalseBool
    } else if * {
      var _ := (true && x == x && !(y == y)) || false; // result is a bool, so anything goes
    } else if * {
      var a: TrueBool := true && x == x;
    } else if * {
      var _ := false || y == y; // result is a bool, so anything goes
      var z: bool := false || y == y; // result is a bool, so anything goes
      var b: FalseBool := false || y == y; // error: (y == y) is not a FalseBool
    } else if * {
      var a: TrueBool := true && y != y; // error: (y != y) is not a TrueBool
    } else if * {
      var b: FalseBool := false || x != x;
    }
  }

  method IntermediateExpressions2(x: TrueBool, y: FalseBool) {
    if * {
      var _ := x ==> !x; // error: !x is not a TrueBool
    } else if * {
      var _ := x <== !x; // error: !x is not a TrueBool
    } else if * {
      var _ := y ==> !y; // error: (y ==> !y) is not a FalseBool
    } else if * {
      var _ := y <== !y; // error: !y is not a FalseBool
    }
  }

  method IntermediateExpressions3(x: TrueBool, y: FalseBool) {
    if * {
      var _ := x && x;
      var _ := x || x;
      var _ := y && y;
      var _ := y || y;
    } else if * {
      var _ := true && x && x;
      var _ := false || x || x; // error: false is not a TrueBool
    } else if * {
      var _ := y || false || y;
      var _ := y && y && true;
      var _ := y || true || y; // error: true is not a FalseBool
    } else if * {
      var a0 := if x then x else !x;
      var a1: FalseBool := if x then y else !y;
      var a2 := if y then !y else y;
      var a3 := if y then x else !x; // error: !x is not a TrueBool
    }
  }

  codatatype Stream = More(Stream)

  method IntermediateExpressions4(s: Stream, k: nat, o: ORDINAL, i: int) returns (ghost x: TrueBool, ghost y: FalseBool) {
    if
    case true =>
      x := s ==#[k] s;
    case true =>
      x := s ==#[o] s;
    case true =>
      x := s !=#[k] s; // error: RHS is not a TrueBool
    case true =>
      x := s !=#[o] s; // error: RHS is not a TrueBool
    case true =>
      y := s ==#[k] s; // error: RHS is not a FalseBool
    case true =>
      y := s ==#[o] s; // error: RHS is not a FalseBool
    case true =>
      y := s !=#[k] s;
    case true =>
      y := s !=#[o] s;
    case true =>
      x := s ==#[i] s; // error: i may be negative
  }
}
