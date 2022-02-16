// RUN: %dafny /compile:0 /functionSyntax:3 "%s" > "%t"
// RUN: %dafny /compile:0 /functionSyntax:migration3to4 "%s" >> "%t"
// RUN: %dafny /compile:0 /functionSyntax:4 "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

function F0(): int // error: 3to4
function method F1(): int // error: v4
ghost function F2(): int // error: v3
ghost function method F3(): int // error: v3, 3to4, v4

twostate function G0(): int
twostate function method G1(): int // error: v3, 3to4, v4
ghost twostate function G2(): int // error: v3, 3to4, v4
ghost twostate function method G3(): int // error: v3 (x2), 3to4 (x2), v4 (x2)

function H0(): int {
  2
} by method {
  return 2;
}
function method H1(): int { // error: v3, 3to4, v4
  2
} by method {
  return 2;
}
ghost function H2(): int { // error: v3, 3to4, 4
  2
} by method {
  return 2;
}
ghost function method H3(): int { // error: v3 (x2), 3to4 (x2), v4 (x2)
  2
} by method {
  return 2;
}

predicate P0() // error: 3to4
predicate method P1() // error: v4
ghost predicate P2() // error: v3
ghost predicate method P3() // error: v3, 3to4, v4

twostate predicate Q0()
twostate predicate method Q1() // error: v3, 3to4, v4
ghost twostate predicate Q2() // error: v3, 3to4, v4
ghost twostate predicate method Q3() // error: v3 (x2), 3to4 (x2), v4 (x2)

predicate R0() {
  true
} by method {
  return true;
}
predicate method R1() { // error: v3, 3to4, v4
  true
} by method {
  return true;
}
ghost predicate R2() { // error: v3, 3to4, v4
  true
} by method {
  return true;
}
ghost predicate method R3() { // error: v3 (x2), 3to4 (x2), v4 (x2)
  true
} by method {
  return true;
}
