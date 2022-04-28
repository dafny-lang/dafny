// RUN: %dafny /compile:0 /print:"%t.print" "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:java "%s" >> "%t"
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
