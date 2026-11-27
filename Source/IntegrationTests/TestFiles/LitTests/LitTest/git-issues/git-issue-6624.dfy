// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Res<T> = Ok(v: T) | Fail {
  predicate IsFailure() { Fail? }
  function PropagateFailure<U>(): Res<U> requires IsFailure() { Fail }
  function Extract(): T requires !IsFailure() { v }
}

class Cell { var f: int }

// The LHS that receives Extract() must differ from the other LHSs, even if the values are equal.
method M(c: Cell, d: Cell, e: Cell) returns (r: Res<int>)
  requires c != e
  modifies c, d, e
{
  c.f, e.f :- Ok(1), 2;
  c.f, d.f :- Ok(1), 2; // error
  var x: int;
  x, x :- Ok(1), 1; // error
  r := Ok(x);
}
