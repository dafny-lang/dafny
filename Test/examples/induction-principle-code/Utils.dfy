// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Utils {
  function method Max(x: int, y: int): int
  {
    if x > y then x else y
  }

  function method {:opaque} MaxF<T>(f: T ~> int, ts: seq<T>, default: int) : (m: int)
    reads f.reads
    requires forall t | t in ts :: f.requires(t)
    requires forall t | t in ts :: default <= f(t)
    ensures if ts == [] then m == default else exists t | t in ts :: f(t) == m
    ensures forall t | t in ts :: f(t) <= m
    ensures default <= m
  {
    if ts == [] then default
    else
      Max(f(ts[0]), MaxF(f, ts[1..], default))
  }

  datatype Result<T> = | Success(value: T) | Failure
  {
    predicate method IsFailure() {
      Failure?
    }

    function method PropagateFailure<U>(): Result<U>
      requires Failure?
    {
      Failure
    }

    function method Extract(): T
      requires Success?
    {
      value
    }
  }

  datatype Option<T> = Some(value: T) | None
}
