// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "../exceptions/VoidOutcomeDt.dfy"

function {:test} PassingTest(): VoidOutcome {
    VoidSuccess
}

function {:test} FailingTest(): VoidOutcome {
    VoidFailure("Whoopsie")
}