// RUN: %exits-with 2 %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Foo

module bar {
  class C {
    var baz : Foo
  }
}
