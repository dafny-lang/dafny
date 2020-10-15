// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file includes verification tests

// ---------------------------------

newtype int8 = x | -128 <= x < 128
newtype smallneg = r | -1.0 <= r <= 0.0

method GoodNewtypeLiterals() returns (b: int8, r: smallneg) {
  if {
    case true =>
      b := -127 - 1;
    case true =>
      b := (-128) as int8;
    case true =>
      b := -128 as int8;  // `-` binds stronger than `as`, so this is the same as the previous line
    case true =>
      b := -128;
    case true =>
      b := - /* some space here */ 128;  // it's two tokens, but it gives one negative literal
  }
  assert b + 64 + 64 == 0;

  if {
    case true =>
      r := -1.0 as smallneg;
    case true =>
      r := -1.0;
  }
}

method BadNewtypeLiterals() returns (b: int8, r: smallneg) {
  if
  case true =>
    b := -(128 as int8);  // error: 128 is not a int8
  case true =>
    b := -128;
    assert 64 + 64 + b == 0;  // error: the subexpression "64 + 64" gives a value that's too large
  case true =>
    r := -(1.0);  // error: 1.0 is not a value of type smallneg
}

// ---------------------------------

method MatchCaseParsing(x: int, p: (int, int)) {
  var y := 0;
  match x {
    case 2 =>
      y := x + y;
    case -1 =>
      y := 3 + x;
    case _ =>
      y := 2;
  }
  assert y == 2;

  match p {
    case (10, 10) =>
      assert p.1 == 10;
    case (10, -10) =>
      assert p.1 == -10;
    case _ =>
  }
}

// ---------------------------------

method GoodBitvectors() returns (v: bv8) {
  if
  case true =>
    v := -(3);  // fine, since this is still a unary-minus expression applied to 3, and - wraps on bitvectors
    assert v == 253;
  case true =>
    v := 200 + 100;  // fine, since 200 and 100 are both bv8 values, and + wraps on bitvectors
    assert v == 44;
}

method BadBitvectors() returns (v: bv8) {
  v := -(1);
  assert v == 1;  // error
}

method Bv0() returns (v: bv0) {
  if * {
    v := -0;  // this is unary-minus expression and is allowed
    assert v == 0;
  } else if * {
    match v
    case 0 =>
  }
}

method Bv1() returns (v: bv1) {
  if * {
    v := -0;
    assert v == 0;
    v := -1;
    assert v == 1;
  } else if * {
    match v
    case 0 =>
    case 1 =>
  } else {
    match v  // error: missing case
    case 0 =>
  }
}
