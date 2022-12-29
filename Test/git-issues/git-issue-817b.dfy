// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Result<T> = Failure(msg: string) | Success(value: T) {
  predicate method IsFailure() { Failure? }
  function method PropagateFailure(): Result<T> requires IsFailure() { this }
  method Extract() returns (t: T) requires !IsFailure() ensures t == this.value { return this.value; }
}

class Cell {
  var data: int
}

method M(c: Cell) returns (r: Result<int>)
  modifies c
  ensures c.data == 7
{
  c.data := 7;
  r := Success(200);
}

method P() returns (r: Result<int>) {
  var a := new int[10];
  var c := new Cell;
  a[c.data] :- M(c);  // this SHOULD be an error, complaining that c.data may not be an index into a
}

method Main() {
  var _ := P();
}
