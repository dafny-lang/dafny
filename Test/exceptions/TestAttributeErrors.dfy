// RUN: %exits-with 3 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "../exceptions/VoidOutcomeDt.dfy"

ghost function {:test} PassingTest(): VoidOutcome { // compile error: function must be compiled to use the {:test} attribute
    VoidSuccess
}

ghost function {:test} FailingTest(): VoidOutcome { // compile error: function must be compiled to use the {:test} attribute
    VoidFailure("Whoopsie")
}
