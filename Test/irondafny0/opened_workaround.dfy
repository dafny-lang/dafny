// RUN: %exits-with 2 %dafny /print:"%t.print" /dprint:"%t.dprint" "%s" /allowAxioms:0 /warningsAsErrors > "%t"
// RUN: %diff "%s.expect" "%t"

module A {

    predicate P() ensures false

    class C
    {
        static ghost method{:axiom} M()
            ensures P();
    }
}

abstract module B {
    import opened A
}

abstract module C {
    import Bee : B       // Works
}
