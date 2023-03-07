// RUN: %run "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  module B
}

module A.B {
  method m() {
    print "Hello, World!\n";
  }
}

method Main() {
  A.B.m();
}
