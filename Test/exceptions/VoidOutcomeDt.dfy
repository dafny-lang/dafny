// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Does not test anything Exceptions-related, but is included by other tests

datatype VoidOutcome =
| VoidSuccess
| VoidFailure(error: string)
{
    predicate method IsFailure() {
        this.VoidFailure?
    }
    function method PropagateFailure(): VoidOutcome requires IsFailure() {
        this
    }
}
