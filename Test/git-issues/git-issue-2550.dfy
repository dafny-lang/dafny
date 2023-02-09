// RUN: %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Foo

module bar {
  class C {
    var baz : Foo
  }
}
