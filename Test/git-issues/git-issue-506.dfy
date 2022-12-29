// RUN: %baredafny run %args --target=cs "%s" > "%t"
// RUN: %baredafny run %args --target=js "%s" >> "%t"
// RUN: %baredafny run %args --target=go "%s" >> "%t"
// RUN: %baredafny run %args --target=java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {

  var a := new int[10];
  var index := 6;
  a[8] := 1;
  a[index], index := 3, index+1;
  assert a[6] == 3;
  assert index == 7;
  print index, " ", a[6], a[7], a[8], "\n";  // Should be: "7 301"
  index, a[index] := index+1, 9;
  assert index == 8;
  assert a[7] == 9;
  assert a[8] == 1; // Assertion is OK
  expect a[8] == 1; // This failed before the bug fix
  print index, " ", a[6], a[7], a[8], "\n";  // Should be "8 391" not "8 309"

  a[index+1], index := 7, 6;
  assert a[9] == 7 && index == 6;
  expect a[9] == 7 && index == 6;

  var o := new F(2);
  var oo := o;
  print o.f, " ", oo.f, "\n";
  assert o.f == 2;
  assert oo.f == 2;
  var ooo := new F(4);
  o.f, o := 5, ooo;
  print o.f, " ", oo.f, "\n";
  assert o.f == 4;
  assert oo.f == 5;
  var oooo := new F(6);
  o, o.f := oooo, 7;
  assert o.f == 6;
  assert ooo.f == 7;
  expect ooo.f == 7;  // This failed before the bug fix
  print o.f, " ", ooo.f, "\n";

  var aa := new int[9,9];
  var j := 4;
  var k := 5;
  aa[j,k] := 8;
  j, k, aa[j,k] := 2, 3, 7;
  print j, " ", k, " ", aa[4,5], " ", aa[2,3], "\n"; // Should be 2 3 7 0
  assert aa[4,5] == 7;
  expect aa[4,5] == 7; // This failed before the bug fix
  j, aa[j,k], k := 5, 6, 1;
  assert j == 5 && aa[2,3] == 6 && k == 1;
  expect j == 5 && aa[2,3] == 6 && k == 1; // This failed before the bug fix
  aa[j,k], k, j := 5, 6, 1;
  assert j == 1 && aa[5,1] == 5 && k == 6;
  expect j == 1 && aa[5,1] == 5 && k == 6;
}

class F {
  var f: int;
  constructor (f: int) ensures this.f == f { this.f := f; }
}
