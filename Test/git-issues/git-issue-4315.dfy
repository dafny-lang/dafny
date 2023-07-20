// RUN: %baredafny run %args -t:cs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M1 {
  class C {
    opaque function f() : bool { true }
  }
}

module M2 refines M1 {
}