---
title: Does Dafny have monadic error handling?
---

## Question

Does Dafny have monadic error handling?

## Answer

Yes, though there is no standard library as yet that includes the needed types.
In particular, see the section of the reference manual on [Update with Failure statements](https://dafny.org/dafny/DafnyRef/DafnyRef#sec-update-failure).

You can define your own monadic error type by following examples in the RM and the draft library. A simple case is
```dafny
datatype Outcome<T> =
            | Success(value: T)
            | Failure(error: string)
{
  predicate method IsFailure() {
    this.Failure?
  }
  function method PropagateFailure<U>(): Outcome<U>
    requires IsFailure()
  {
    Failure(this.error) // this is Outcome<U>.Failure(...)
  }
  function method Extract(): T
    requires !IsFailure()
  {
    this.value
  }
}
```
