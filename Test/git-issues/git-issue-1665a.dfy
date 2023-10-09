// RUN: %exits-with 4 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Additional tests

module TypeCasts {
  method P(x: int) {
    match x
    case m =>
  }

  method M0(x: int) {
    match x
    case n: nat => // error: x may be negative
      print n, "\n";
  }

  method M1(x: int) {
    match x
    case n: nat => // error: x may be negative
  }

  method M2(x: int) {
    match x
    case _: nat => // error: x may be negative
  }

  method M2'(x: int) {
    match x
    case _ => // fine
  }

  method M2''(x: int) {
    match x
    case _: int => // fine
  }

  method M3(x: int) {
    match x
    case 3 =>
    case _: nat => // error: x may be negative
  }

  function F(x: int): int {
    match x
    case n: nat => n // error: x may be negative
  }
}
