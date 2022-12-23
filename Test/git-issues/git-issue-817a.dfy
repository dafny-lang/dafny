// RUN: %testDafnyForEachCompiler "%s"

datatype Result<T> = Failure(msg: string) | Success(value: T) {
  predicate method IsFailure() { Failure? }
  function method PropagateFailure(): Result<T> requires IsFailure() { this }
  method Extract() returns (t: T) requires !IsFailure() ensures t == this.value { return this.value; }
}

class Cell {
  var data: int
}

method M(a: array<int>, c: Cell) returns (r: Result<int>)
  requires a.Length == 10
  modifies a, c
  ensures r.Success? ==> r.value == 200
  ensures c.data == 9;
{
  a[7] := 180;
  c.data := 9;
  r := Success(200);
}

method P() returns (r: Result<int>){
  var a := new int[10];
  a[7] := 321;
  a[9] := 142;
  var c := new Cell;
  c.data := 7;
  // The following statement should first compute the l-value for a[c.data], namely a[7].
  // Then it should call M, which has side effects on a,c.
  // Then, if M is successful, it should set a[7] to 200.
  a[c.data] :- M(a, c);
  assert a.Length == 10;
  assert a[7] == 200;
  assert c.data == 9;
  print c.data, " ", a[7], " ", a[9], "\n"; // 9 200 142
}

method Main() {
  var _ := P();
}
