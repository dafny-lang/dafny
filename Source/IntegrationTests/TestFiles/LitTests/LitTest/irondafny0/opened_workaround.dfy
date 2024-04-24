// RUN: %exits-with 3 %build %s > "%t"
// RUN: %diff "%s.expect" "%t"

module A {

    ghost predicate P() ensures false

    class C
    {
        static ghost method {:axiom} M()
            ensures P()
    }
}

abstract module B {
    import opened A
}

abstract module C {
    import Bee : B       // Works
}
