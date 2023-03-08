// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Does not test anything Exceptions-related, but is included by other tests

datatype VoidOutcome =
| VoidSuccess
| VoidFailure(error: string)
{
    predicate IsFailure() {
        this.VoidFailure?
    }
    function PropagateFailure(): VoidOutcome requires IsFailure() {
        this
    }
}
