// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Foo {
    function Fun(): () {
        calc { 0; }
        ()
    }
}

abstract module Bar {
    import Foo' : Foo
}
