// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Foo {
    ghost function Fun(): () {
        calc { 0; }
        ()
    }
}

abstract module Bar {
    import Foo' : Foo
}
