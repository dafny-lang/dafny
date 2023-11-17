// RUN: %testDafnyForEachResolver "%s"


module M1 {
  class C {
    opaque function f() : bool { true }
  }
}

module M2 refines M1 {
}
