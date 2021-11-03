// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class MyClass {
  method M() returns (res: Result<real>) {
    var x :- P();
  }
}

method P() returns (res: Result<real>)

datatype Result<T> = Success(value: T) | Failure {
  compiled predicate IsFailure() { Failure? }
  compiled function PropagateFailure(): Result<T> { this }
  compiled function Extract(): int { 5 }
}
