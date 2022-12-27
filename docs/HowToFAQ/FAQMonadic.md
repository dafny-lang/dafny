---
title: Does Dafny have monadic error handling?
---

## Question

Does Dafny have monadic error handling?

## Answer

Yes.

In particular, see the section of the reference manual on [Update with Failure statements](../DafnyRef/DafnyRef#sec-update-failure).
The (draft) standard library includes [some types needed for error handling](https://github.com/dafny-lang/libraries/blob/master/src/Wrappers.dfy).

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
