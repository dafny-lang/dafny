// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class MyClass {
  method M() returns (res: Result<real>) {
    var x :- P();
  }
}

method P() returns (res: Result<real>)

datatype Result<T> = Success(value: T) | Failure {
  predicate method IsFailure() { Failure? }
  function method PropagateFailure(): Result<T> { this }
  function method Extract(): int { 5 }
}
