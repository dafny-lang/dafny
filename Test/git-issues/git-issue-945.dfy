// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  datatype Result<T> = Success(value: T) | Failure {
    compiled predicate IsFailure() { Failure? }
    compiled function PropagateFailure(): Result<T> { this }
    compiled function Extract(): int { 5 }
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

