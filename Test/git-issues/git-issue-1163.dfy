// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function F(i: int): int

method M() {
  ghost var f := old(i => F(i));  // the translation of this once had crashed the verifier
}
