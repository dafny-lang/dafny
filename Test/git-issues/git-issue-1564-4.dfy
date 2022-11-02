// RUN: %dafny /compile:0 /functionSyntax:4 /env:0 /dprint:- "%s" > "%t"
// RUN: %dafny /compile:0 /functionSyntax:experimentalDefaultGhost /env:0 /dprint:- "%s" >> "%t"
// RUN: %dafny /compile:0 /functionSyntax:experimentalDefaultCompiled /env:0 /dprint:- "%s" >> "%t"
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
