// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  datatype Result<T> = Success(value: T) | Failure {
    predicate method IsFailure() { Failure? }
    function method PropagateFailure(): Result<T> { this }
    function method Extract(): int { 5 }
  }

  method P() returns (ret: Result<real>)
}

module B {
  import A

  method M() returns (res: A.Result<real>)
  {
    var x :- A.P();
  }
}

