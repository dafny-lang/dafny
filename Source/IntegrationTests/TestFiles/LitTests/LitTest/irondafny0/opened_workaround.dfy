// RUN: %exits-with 2 %dafny /print:"%t.print" /dprint:"%t.dprint" "%s" /allowAxioms:0 /warningsAsErrors > "%t"
// RUN: %diff "%s.expect" "%t"

module A {

<<<<<<< HEAD:Test/irondafny0/opened_workaround.dfy
    predicate P() ensures false

    class C
    {
        static ghost method{:axiom} M()
            ensures P();
=======
    ghost predicate P()

    class C
    {
        static method{:axiom} M()
            ensures P()
>>>>>>> origin/master:Source/IntegrationTests/TestFiles/LitTests/LitTest/irondafny0/opened_workaround.dfy
    }
}

abstract module B {
    import opened A
}

abstract module C {
    import Bee : B       // Works
}
