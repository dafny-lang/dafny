// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module FOO {
  //  two fields are needed
  datatype D = D(
    f1: nat,
    f2: nat
  )

  function f(d : D) : nat
    ensures f(d) != 0

  const D0 := D(0, 0)

  //  Similar outcomes occur using f1 or f2
  const C1 :=  D0.(f2 := f(D0))

  class E {
    var a : D
    constructor ()  {
      a := C1;
    }
  }
}
