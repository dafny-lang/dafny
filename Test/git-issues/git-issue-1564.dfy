// RUN: ! %baredafny verify %args --function-syntax:3 "%s" > "%t"
// RUN: ! %baredafny verify %args --function-syntax:migration3to4 "%s" >> "%t"
// RUN: ! %baredafny verify %args --function-syntax:4 "%s" >> "%t"
// RUN: ! %baredafny verify %args --function-syntax:experimentalDefaultGhost "%s" >> "%t"
// RUN: ! %baredafny verify %args --function-syntax:experimentalDefaultCompiled "%s" >> "%t"
// RUN: ! %baredafny verify %args --function-syntax:experimentalPredicateAlwaysGhost "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

function F0(): int // error: 3to4
function method F1(): int // error: v4, aGhost
ghost function F2(): int // error: v3
ghost function method F3(): int // error

twostate function G0(): int
twostate function method G1(): int // error
ghost twostate function G2(): int // error
ghost twostate function method G3(): int // error

function H0(): int {
  2
} by method {
  return 2;
}
function method H1(): int { // error
  2
} by method {
  return 2;
}
ghost function H2(): int { // error
  2
} by method {
  return 2;
}
ghost function method H3(): int { // error
  2
} by method {
  return 2;
}

predicate P0() // error: 3to4
predicate method P1() // error: v4, aGhost
ghost predicate P2() // error: v3, aGhost
ghost predicate method P3() // error

twostate predicate Q0()
twostate predicate method Q1() // error
ghost twostate predicate Q2() // error
ghost twostate predicate method Q3() // error

predicate R0() {
  true
} by method {
  return true;
}
predicate method R1() { // error
  true
} by method {
  return true;
}
ghost predicate R2() { // error
  true
} by method {
  return true;
}
ghost predicate method R3() { // error
  true
} by method {
  return true;
}
