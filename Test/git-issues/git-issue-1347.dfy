// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Foo {
  datatype T = TX()
  datatype U = U
  datatype V = TV()
  datatype W0 = W0()
  datatype W1 = W1()
}

module Bar {
  datatype T = TY()
  datatype U = U
  ghost function V(): int
  datatype W0 = W0
  datatype W1 = W1
}

module Consumer {
  import opened Foo
  import opened Bar

  type W0 = Foo.W0
  type W1 = Bar.W1

  // The following export set once caused a crash in Dafny, because of the
  // ambiguously import-opened T (and U).
  export
    provides Foo, Bar
}
