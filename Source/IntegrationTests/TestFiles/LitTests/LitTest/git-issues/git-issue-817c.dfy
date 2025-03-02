// RUN: %exits-with 4 %verify --relax-definite-assignment --allow-deprecation --type-system-refresh=false --general-newtypes=false "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Result<T> = Failure(msg: string) | Success(value: T) {
  predicate IsFailure() { Failure? }
  function PropagateFailure(): Result<T> requires IsFailure() { this }
  function Extract(): T requires !IsFailure() { this.value }
}

class Cell {
  var data: int;
  var data2: int;

  method MM() returns (r: Result<int>, i: int, j: int) {
    return Success(200), 3, 4;
  }

  method PA() returns (r: Result<int>)
    modifies this;
  {
    var k: int;
    data, this.data, k :- MM(); // ERROR
  }

  method P0() returns (r: Result<int>)
    modifies this;
  {
    var k: int;
    this.data, data, k :- MM(); // ERROR
  }
}

method M() returns (r: Result<int>, i: int, j: int)
  ensures r.Success? ==> r.value == 200
  ensures i == 3 && j == 4;
{
  r := Success(200);
  i := 3;
  j := 4;
}

method P1() returns (r: Result<int>){
  var k: int;
  var i: int;
  k, i, i :- M(); // ERROR
}

method P2() returns (r: Result<int>){
  var k: int;
  var i: int;
  i, i, k :- M(); // ERROR
}

method P3() returns (r: Result<int>) {
  var k: int;
  var c := new Cell;
  var cc := new Cell;
  var ccc := c;
  c.data, cc.data, k :- M(); // OK
}

method P4() returns (r: Result<int>) {
  var k: int;
  var c := new Cell;
  var cc := new Cell;
  var ccc := c;
  c.data, ccc.data, k :- M(); // ERROR
}

method P5() returns (r: Result<int>) {
  var k: int;
  var c := new Cell;
  var cc := new Cell;
  var ccc := c;
  k, c.data, ccc.data :- M(); // ERROR
}

method P6() returns (r: Result<int>) {
  var k: int;
  var a := new int[10];
  var aa := new int[10];
  var aaa := a;
  k, a[2], aaa[2] :- M(); // ERROR
}

method P7() returns (r: Result<int>) {
  var k: int;
  var a := new int[10];
  var aa := new int[10];
  var aaa := a;
  a[2], k, aaa[2] :- M(); // ERROR
}

method P8() returns (r: Result<int>) {
  var k: int;
  var a := new int[10];
  var aa := new int[10];
  var aaa := a;
  a[2], k, aaa[3] :- M(); // OK
  a[2], k, aa[2] :- M(); // OK
}

