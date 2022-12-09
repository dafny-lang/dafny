// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  class E {}
  class D { var e: E; constructor(e: E) { this.e := e; } }
}

module B {
  datatype E = E
  datatype Box = Boxed(e: E)
}

method testF(a: A.D) {
  var b := B.Boxed(a.e);
}
