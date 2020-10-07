// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Result<T> = Failure(msg: string) | Success(value: T) {
  predicate method IsFailure() { Failure? }
  function method PropagateFailure(): Result<T> requires IsFailure() { this }
  method Extract() returns (t: T) requires !IsFailure() ensures t == this.value { return this.value; }
}

class Cell {
  var data: int;
}

method M() returns (r: Result<int>, i: int, j: int)
  ensures r.Success? ==> r.value == 200
  ensures i == 3 && j == 4;
{
  r := Success(200);
  i := 3;
  j := 4;
}

method P() returns (r: Result<int>){
  var k: int;
  var i: int;
  i, i, k :- M();
}

method Main() {
  var _ := P();
}
