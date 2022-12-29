// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Does not test anything Exceptions-related, but is included by other tests

datatype Outcome<T> =
| Success(value: T)
| Failure(error: string)
{
    predicate method IsFailure() {
        this.Failure?
    }
    function method PropagateFailure<U>(): Outcome<U> requires IsFailure() {
        Failure(this.error)
    }
    function method Extract(): T requires !IsFailure() {
        this.value
    }
}
