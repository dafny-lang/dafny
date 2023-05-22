// RUN: %exits-with 3 %dafny /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {

    ghost predicate P()

    class C
    {
        static method{:axiom} M()
            ensures P();
    }
}

abstract module B {
    import opened A
}

abstract module C {
    import Bee : B       // Works
}
