// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=js "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=go "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=java "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype PhantomData<T> = PhantomData(ghost value: T)

method Test0(t0: (ghost int)) { print "Test0: ", t0, "\n"; }
method Test1(t1: (ghost int, int)) { print "Test1: ", t1, "\n"; }
method Test2(t2: (int, ghost int, int)) { print "Test2: ", t2, "\n"; }
method Test3(t3: ((ghost int), (ghost int, int), ghost int)) { print "Test3: ", t3, "\n"; }

method Main() {
  var p := PhantomData(123);
  var t0, t1, t2, t3;
  Test0(t0);
  Test1(t1);
  Test2(t2);
  Test3(t3);
  t0 := (ghost 00);
  t1 := (ghost 11, 22);
  t2 := (33, ghost 44, 55);
  t3 := ((ghost 66), (ghost 77, 88), ghost 99);
  Test0(t0);
  Test1(t1);
  Test2(t2);
  Test3(t3);
  TestDestructors();
  TestMatchDestructions();
  var sss := TestSingletons();
  print sss.1, "\n"; // 1213
  MoreSingletonTests();
}

method TestDestructors() {
  var u := (100, 200);
  print u.0, " ", u.1, "\n"; // 100 200

  var a, b, c, d; // will be initialized to default values
  print a, " ", b, " ", c, " ", d, "\n"; // 

  a := (5, ghost 7, 9);
  b := (ghost 9, ghost 16, 25, 36);
  c := (ghost 7, 5);
  d := (ghost 9, ghost 16, 25);

  print a.2, " ", b.2, "\n"; // 9 25
  print c.1, " ", d.2, "\n"; // 5 25
}

method TestMatchDestructions() {
  var e := (ghost 15);
  var a := (5, ghost 7, 9);
  var b := (ghost 9, ghost 16, 25, 36);
  var c := (ghost 7, 5);
  var d := (ghost 9, ghost 16, 25);

  // match statements

  match e {
    case (_) => print e, "\n"; // ()
  }
  match a {
    case (x, _, y) => print x, " ", y, "\n"; // 5 9
  }
  match b {
    case (_, _, x, y) => print x, " ", y, "\n"; // 25 36
  }
  match c {
    case (_, x) => print x, "\n"; // 5
  }
  match d {
    case (_, _, x) => print x, "\n"; // 25
  }

  // match expressions

  var ee := match e case (_) => e;
  var aa := match a case (x, _, y) => x + y; // 14
  var bb := match b case (_, _, x, y) => x + y; // 61
  var cc := match c case (_, x) => x; // 5
  var dd := match d case (_, _, x) => x; // 25
  print ee, " ", aa, " ", bb, " ", cc, " ", dd, "\n";
}

method TestSingletons() returns (r: (ghost int, int, ghost real, ghost real)) {
  var s0 := Singleton0();
  var s1 := Singleton1();
  print s1, "\n"; // as usual for datatypes, ghost components are omitted
  var s2 := Singleton2();
  var c := SingletonConst;
  var u := (if s0.1 == s1.0 then 1100 else 1099) + s2.2 + c.0;
  assert u == 1212;
  r := (ghost u + 50, u, ghost s0.1, ghost s2.0);

  var x;
  match s2 {
    case (a, b, c, d) => x := c;
  }
  x := x + match s2 case (a, b, c, d) => 1 - c;
  assert x == 1;

  return r.(1 := r.1 + x);
}

function method Singleton0(): (ghost int, real) {
  (ghost 2, 3.2)
}

function method Singleton1(): (real, ghost int) {
  (3.2, ghost 2)
}

function method Singleton2(): (ghost real, ghost (), int, ghost char) {
  (ghost 5.0, ghost (), 100, ghost 'D')
}

const SingletonConst := (12, ghost 13)

type SX = (ghost int, int, ghost int)
type SX2 = (SX, ghost real)
datatype SX3 = SX3(a: SX, ghost b: real)

method MoreSingletonTests() {
  var r := (ghost 2, 3, ghost 4);
  print r, "\n"; // 3
  var arr := new SX[20];
  arr[3] := (ghost 200, 100, ghost 400);
  PrintOneSx(arr[3]); // 100
  print arr[0], " ", arr[3], "\n"; // 0 100
  UpdateArray(arr, (ghost 99, 9, ghost 999));
  print arr[1], " ", arr[2], "\n"; // 0 9
  UpdateSxArray(arr, (ghost 99, 19, ghost 999));
  print arr[4], " ", arr[5], "\n"; // 0 19

  var sx2 := (arr[5], ghost 2.0);
  print sx2, "\n"; // 19
  var arr2 := new SX2[20];
  UpdateArray(arr2, ((ghost 5, 15, ghost 25), ghost 3.0));
  print arr2[1], " ", arr2[2], "\n"; // 0 15

  var sx3 := SX3(arr[2], 4.0);
  print sx3, "\n"; // 9
  var arr3 := new SX3[20];
  UpdateArray(arr3, sx3);
  print arr3[1], " ", arr3[2], "\n"; // 0 9
}

method PrintOneSx(g: SX) {
  print g, "\n";
}

method UpdateArray<T(0)>(arr: array<T>, t: T)
  requires 10 <= arr.Length
  modifies arr
{
  var tt: T;
  arr[1] := tt;
  arr[2] := t;
}

method UpdateSxArray(arr: array<SX>, t: SX)
  requires 10 <= arr.Length
  modifies arr
{
  var tt: SX;
  arr[4] := tt;
  arr[5] := t;
}
