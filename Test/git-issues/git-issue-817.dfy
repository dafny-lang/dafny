// RUN: %testDafnyForEachCompiler "%s"

datatype Result<T> = Failure(msg: string) | Success(value: T) {
  predicate IsFailure() { Failure? }
  function PropagateFailure(): Result<T> requires IsFailure() { this }
  function Extract(): (t: T) requires !IsFailure() ensures t == this.value { this.value }
}

class D {
  constructor (vv: int) ensures v == vv { v := vv; }
  var v: int
}
method Main() {
  var _ := m();
  var _ := mm();
  var _ := mmm();
}

method m() returns (rr: Result<int>) {
  var d0 := new D(42);
  var r := Success(100);
  var d: D := new D(90);
  var dd: D := d;
  print d.v, " ", dd.v, "\n"; // 90 90
  assert d.v == 90 && dd.v == 90;
  expect d.v == 90 && dd.v == 90;

  d.v, d :- r, d0;
  print d.v, " ", dd.v, " ", d != dd, "\n"; // 42 100 true
  assert d.v == 42;
  assert dd.v == 100;
  expect d.v == 42 && dd.v == 100;
  rr := *;
}

method mm() returns (rr: Result<int>) {
  var d0 := new int[1]; d0[0] := 42;
  var r := Success(100);
  var d := new int[1]; d[0] :=  90;
  var dd := d;
  print d[0], " ", dd[0], "\n"; // 90 90
  assert d[0] == 90 && dd[0] == 90;
  expect d[0] == 90 && dd[0] == 90;

  d[0], d :- r, d0;
  print d[0], " ", dd[0], " ", d != dd, "\n"; // 42 100 true
  assert d[0] == 42 && dd[0] == 100;
  expect d[0] == 42 && dd[0] == 100;
  rr := *;
}

method mmm() returns (rr: Result<int>) {
  var d0 := new int[1,1]; d0[0,0] := 42;
  var r := Success(100);
  var d := new int[1,1]; d[0,0] :=  90;
  var dd := d;
  print d[0,0], " ", dd[0,0], "\n"; // 90 90
  assert d[0,0] == 90 && dd[0,0] == 90;
  expect d[0,0] == 90 && dd[0,0] == 90;

  d[0,0], d :- r, d0;
  print d[0,0], " ", dd[0,0], " ", d != dd, "\n"; // 42 100 true
  assert d[0,0] == 42 && dd[0,0] == 100;
  expect d[0,0] == 42 && dd[0,0] == 100;
  rr := *;
}

class C {
  var x: int

  method m() returns (rr: Result<int>)
    modifies this
  {
    var y: int;
    var r := Success(100);
    x, y :- r, 100;
    rr := r;
  }
}
