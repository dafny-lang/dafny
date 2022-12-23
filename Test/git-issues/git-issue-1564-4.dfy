// RUN: %baredafny verify %args --function-syntax:4 --print:- "%s" > "%t"
// RUN: %baredafny verify %args --function-syntax:experimentalDefaultGhost --print:- "%s" >> "%t"
// RUN: %baredafny verify %args --function-syntax:experimentalDefaultCompiled --print:- "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

ghost function F0(): int
function F1(): int

twostate function G0(): int

function H0(): int {
  2
} by method {
  return 2;
}

ghost predicate P0()
predicate P1()

twostate predicate Q0()

predicate R0() {
  true
} by method {
  return true;
}
