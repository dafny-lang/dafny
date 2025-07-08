// RUN: %exits-with 2 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Result<T> = Success(value: T) | Failure(error: string)
{
  predicate IsFailure() {
    Failure?
  }
  function PropagateFailure<U>(): Result<U>
    requires Failure?
  {
    Failure(this.error)
  }
  function Extract(): T
    requires Success?
  {
    value
  }
}

method mn() returns (r: Result<int>)
{
  var t, k, u :- m(1);
  var tt :- m(1);
}

method mn1() returns (out: int)
{
  var t, k, u :- m(1);
  var tt :- m(1);
}

method m(i: int) returns (r: Result<int>, o: int)
{
  if i < 0 { return Failure("negative"), i+i; }
  return Success(i), i+i;
}


