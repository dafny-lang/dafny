// RUN: %exits-with 2 %run "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  module B
}


method Main() {
  A.B.m();
}
