// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Does not test anything Exceptions-related, but is included by other tests

datatype Outcome<T> =
| Success(value: T)
| Failure(error: string)
{
    predicate IsFailure() {
        this.Failure?
    }
    function PropagateFailure<U>(): Outcome<U> requires IsFailure() {
        Failure(this.error)
    }
    function Extract(): T requires !IsFailure() {
        this.value
    }
}
