// RUN: %dafny /compile:0 /typeSystemRefresh:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Bar {
  class Foo {
    // The following line once used to give an error, because newtype "b1" had not yet been resolved
    const c0: b1 := 4
  }
  newtype b1 = x | 0 <= x < 11/2
}

module Zar {
  newtype b1 = x | 0 <= x < 11/2
  class Foo {
    const c0: b1 := 4
  }
}
