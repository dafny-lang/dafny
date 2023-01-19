// RUN: %dafny /compile:4 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/// Check that the compiler accepts `:- assume {:axiom} …`.

datatype Result<+T> = | Success(value: T) | Failure {
  predicate method IsFailure() { Failure? }
  function method PropagateFailure<U>(): Result<U> requires Failure? { Failure() }
  function method Extract(): T requires Success? { value }
}

method Main() {
  var x: int :- assume {:axiom} Success(1);
  print x;
}
