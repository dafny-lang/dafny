// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method M1() returns (x: int)
{
  print "hello, M1\n";
}

method M2() returns (x: int, ghost y: int)
{
  print "hello, M2\n";
}

method M3() returns (x: int, ghost y: int, z: int)
{
  print "hello, M3\n";
}

method N0<T(0)>() returns (x: T, ghost y: int, z: T)
{
  print "hello, N0\n";
}

method N1<T(0)>() returns (x: int, ghost y: T, z: int)
{
  print "hello, N1\n";
}

method Main() {
  P0();  // calls M2
  P1();  // calls M2
  P2();  // calls M3
  P3();  // calls M1
  var _ := P4();  // calls M1
  P5();  // calls M1, M2, M3
  P6();  // calls N0, N1
}

method P0() {
  ghost var a, b := M2();  // regression test: compiler once emitted assignment to a
}

method P1() {
  ghost var a, b;
  a, b := M2();  // regression test: compiler once emitted assignment to a
}

method P2() {
  ghost var a, b;
  var c;
  a, b, c := M3();  // regression test: compiler once emitted assignment to a
}

method P3() {
  ghost var a := M1();  // regression test: compiler once emitted assignment to a
}

method P4() returns (ghost a: int) {
  a := M1();  // regression test: compiler once emitted assignment to a
}

method P5() {
  var _ := M1();
  var _, _ := M2();
  var _, _, _ := M3();
}

method P6() {
  var a: (bool, real);
  ghost var b: int;
  var c: (bool, real);
  a, b, c := N0();  // regression test: compiler once used type of wrong parameter when considering a cast

  var k: int;
  ghost var l: (bool, real);
  var m: int;
  k, l, m := N1();  // regression test: compiler once used type of wrong parameter when considering a cast
}
