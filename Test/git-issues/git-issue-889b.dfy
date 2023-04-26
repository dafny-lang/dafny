// RUN: %exits-with 2 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file tests resolution errors

module BitvectorLiterals {
  method Bitvectors() returns (v: bv8) {
    if
    case true =>
      v := 300; // error: literal 300 too large to be a bv8
    case true =>
      v := 200 + 100;  // fine
    case true =>
      v := -3;  // this is a unary-minus expression
    case true =>
      v := -(3);
    case true =>
      v := -300; // error: literal 300 too large to be a bv8
  }

  method MatchStmt(v: bv8) {
    match v
    case -3 =>  // error: unary minus not allowed in case pattern
    case -0 =>  // error: unary minus not allowed in case pattern
    case _ =>
  }

  method MatchExpr(v: bv8) returns (r: int) {
    r := match v
      case -3 => 10  // error: unary minus not allowed in case pattern
      case -0 => 11  // error: unary minus not allowed in case pattern
      case _ => 12;
  }

  method Bv0() returns (v: bv0) {
    v := -0;  // fine, this is a unary-minus expression
    assert v == 0;
    match v
    case -0 =>  // error: unary minus not allowed in case pattern
}
}

module ORDINALs {
  method M() {
    var o: ORDINAL;
    o := -2;  // error: ORDINAL does not support unary minus
  }
}

module MatchORDINAL {
  method Match(o: ORDINAL) {
    match o
    case 2 =>
    case -2 =>  // error: unary minus not allowed in case pattern
    case -0 =>  // error: unary minus not allowed in case pattern
    case _ =>
  }
}
