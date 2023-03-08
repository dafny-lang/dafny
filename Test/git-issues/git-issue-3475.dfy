// RUN: ! %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Test {

  method foo() returns (y: int)
  {
    x :- bar();
  }
  method bar() returns (y: Result<int>) // return type doesn't matter

  datatype Result<+U> =
    | Success(value: U)
    | Failure(exception: string)
  {

    ghost function Lift<V>(f: U --> V): Result<V>
      requires this.Success? ==> f.requires(value)
    {
      match this {
        case Success(v) => Success(f(v))
        case Failure(e) => Failure(e)
      }
    }

    predicate IsFailure() {
      Failure?
    }

    function PropagateFailure<V>(): (ret: Result<V>)
      requires IsFailure()
    {
      Failure(exception)
    }

    function Extract(): U
      requires !IsFailure()
    {
      value
    }
  }
}
