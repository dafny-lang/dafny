// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  datatype Result<T> = Success(value: T) | Failure {
    predicate IsFailure() { Failure? }
    function PropagateFailure(): Result<T> { this }
    function Extract(): int { 5 }
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

