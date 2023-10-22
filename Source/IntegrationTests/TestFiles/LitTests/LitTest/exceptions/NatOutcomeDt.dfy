// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Does not test anything Exceptions-related, but is included by other tests

datatype NatOutcome =
| NatSuccess(value: nat)
| NatFailure(error: string)
{
    predicate IsFailure() {
        this.NatFailure?
    }
    function PropagateFailure(): NatOutcome requires IsFailure() {
        this
    }
    function Extract(): nat requires !IsFailure() {
        this.value
    }
}
