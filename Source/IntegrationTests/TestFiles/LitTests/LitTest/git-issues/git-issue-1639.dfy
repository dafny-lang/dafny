// RUN: %testDafnyForEachResolver "%s"


module Foo {
    ghost function Fun(): () {
        calc { 0; }
        ()
    }
}

abstract module Bar {
    import Foo' : Foo
}
