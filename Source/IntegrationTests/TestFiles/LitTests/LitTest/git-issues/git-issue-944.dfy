// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class MyClass {
  method M() returns (res: Result<real>) {
    var x :- P();
  }
}

method P() returns (res: Result<real>)

datatype Result<T> = Success(value: T) | Failure {
  predicate IsFailure() { Failure? }
  function PropagateFailure(): Result<T> { this }
  function Extract(): int { 5 }
}
