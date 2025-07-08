// RUN: %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Utils {
  function Max(x: int, y: int): int
  {
    if x > y then x else y
  }

  function {:opaque} MaxF<T(!new)>(f: T ~> int, ts: seq<T>, default: int) : (m: int)
    reads set x, y | x in ts && y in f.reads(x) :: y
    requires forall t : T | t in ts :: f.requires(t)
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
    predicate IsFailure() {
      Failure?
    }

    function PropagateFailure<U>(): Result<U>
      requires Failure?
    {
      Failure
    }

    function Extract(): T
      requires Success?
    {
      value
    }
  }

  datatype Option<T> = Some(value: T) | None
}
