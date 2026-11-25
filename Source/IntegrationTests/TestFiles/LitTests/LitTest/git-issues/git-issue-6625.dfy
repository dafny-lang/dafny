// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Result<T> = Success(value: T) | Failure(error: string) {
  predicate IsFailure() { Failure? }
  function PropagateFailure<U>(): Result<U> requires Failure? { Failure(error) }
  function Extract(): T requires Success? { value }
}

method M() returns (r: int, y: int) { r := 1; y := 2; }
method MR() returns (r: Result<int>, y: int) { r := Success(1); y := 2; }

datatype D = A | B

method InMatchAssign(d: D) returns (out: int)
{
  var x: int;
  match d
  case A =>
    x, x := M();  // error: duplicate LHS
    out := x;
  case B =>
    out := 0;
}

method InMatchAssignOrReturn(d: D) returns (out: Result<int>)
{
  var x: int;
  match d
  case A =>
    x, x :- MR();  // error: duplicate LHS
    out := Success(x);
  case B =>
    out := Failure("b");
}
