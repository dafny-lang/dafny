// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


trait P1
{
  method N0() {
    var a: array<int>;
    if (5 < a.Length) {
      a[5] := 12;  // error: violates modifies clause
    }
  }

  method Mul(x: int, y: int) returns (r: int)
    requires 0 <= x && 0 <= y;
    ensures r == x*y;
    decreases x;
}

class C1 extends P1
{
  method Mul(x: int, y: int) returns (r: int)
    requires 0 <= x && 0 <= y;
    ensures r == x*y;
    decreases x;
  {
    if (x == 0) {
      r := 0;
    } else {
      var m := Mul(x-1, y);
      r := m + y;
    }
  }

  method Testing(arr:array<int>)
    requires arr.Length == 2 && arr[0]== 1 && arr[1] == 10;
  {
    N0(); //calling parent trait methods
    var x := 2;
    var y := 5;
    var z := Mul(x,y);
    assert (z == 10);
  }
}
