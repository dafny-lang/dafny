// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// When a function call violates two preconditions at the same time, it causes
// two errors to be reported for the same token

method A(x: int)
  requires x > 0
  requires x < 0
{}

method B(x: int) {
  A(x);
}

function fA(x: int): int
  requires x > 0
  requires x < 0 { 1 }

function fB(x: int): int { fA(x) }
