// RUN: %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class A {
  var a: array<array<int>>
  constructor(b: array<array<int>>) {
    var c := b;
    a := b;
  }
}
method sub(a: array<array<int>>)
  requires a.Length > 0
  requires a[0].Length > 0
{
  print a[0][0], " ";
  var b := a;
  print b[0][0], "\n";
}
method Main() {
  var a := new array<int>[2];
  a[0] := new int[2];
  a[0][0] := 42;
  print a[0][0], " ";
  sub(a);
  var b := new A(a);
  MoreTests();
}

method MoreTests() {
  TestA();
  TestB();
  TestC();
  TestD();
  TestE();
}

method TestA() {
  var a := new int[2];
  var b := new array<int>[2];
  var c := new array<array2<int>>[2];
  var d := new array2<array<int>>[2];
  var e := new array4<array3<int>>[2];
  a[0] := 5000;
  b[0] := new int[10];
  b[0][4] := 5000;
  c[0] := new array2<int>[10];
  c[0][4] := new int[70,80];
  c[0][4][63,73] := 5000;
  d[0] := new array<int>[70,80];
  d[0][63,73] := new int[10];
  d[0][63,73][4] := 5000;
  e[0] := new array3<int>[12,2,3,15];
  e[0][11,1,2,14] := new int[20,1,1];
  e[0][11,1,2,14][18,0,0] := 5000;
  print a[0], " ", b[0][4], " ";
  print c[0][4][63,73], " ", d[0][63,73][4], " ";
  print e[0][11,1,2,14][18,0,0], "\n";
}

method TestB() {
  var a := new int[2,3];
  var b := new array<int>[2,3];
  var c := new array<array2<int>>[2,3];
  var d := new array2<array<int>>[2,3];
  var e := new array4<array3<int>>[2,3];
}

method TestC() {
  var a := new int[2];
  var b := new array?<int>[2];
  var c := new array?<array2?<int>>[2];
  var d := new array2?<array?<int>>[2];
  var e := new array4?<array3?<int>>[2];
}

method TestD() {
  var a: array2<int> := new int[3,2];
  var b: array<array2<int>> := new array2<int>[5];
  b := new array2<int>[5][a, a, a, a, a];
  b := new array2<int>[5](_ => a);
  var c: array3<array<array2<int>>> := new array<array2<int>>[5,4,3];
  c := new array<array2<int>>[5,4,3]((_,_,_) => b);
}

method TestE() {
  var a: array2?<int> := new int[3,2];
  var b: array?<array2?<int>> := new array2?<int>[5];
  b := new array2?<int>[5][a, a, a, a, a];
  b := new array2?<int>[5](_ => a);
  var c: array3?<array?<array2?<int>>> := new array?<array2?<int>>[5,4,3];
  c := new array?<array2?<int>>[5,4,3]((_,_,_) => b);
  var d: array15?<int>;
  var e: array16<int>;
}
