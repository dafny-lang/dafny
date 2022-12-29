// RUN: %exits-with 3 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "../exceptions/VoidOutcomeDt.dfy"

function {:test} PassingTest(): VoidOutcome { // compile error: function must be compiled to use the {:test} attribute
    VoidSuccess
}

function {:test} FailingTest(): VoidOutcome { // compile error: function must be compiled to use the {:test} attribute
    VoidFailure("Whoopsie")
}
