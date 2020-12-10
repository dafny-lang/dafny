// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class MyClass {
  method M() returns (res: Result<real>) {
    var x :- P();  // this currently generates resolution errors
  }
}

method P() returns (res: Result<real>)

// The details of the following type are not relevant to the error, but are needed to make a complete repro
datatype Result<T> = Success(value: T) | Failure {
  predicate method IsFailure() { Failure? }
  function method PropagateFailure(): Result<T> { this }
  function method Extract(): int { 5 }
}

