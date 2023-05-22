// RUN: %testDafnyForEachCompiler "%s"

datatype D = Nil | MM | D(x: int, tail: D)

method M1() {

var D(a,b) := D(1, D(2, Nil)); //OK
assert a == 1;
assert b == D(2,Nil);
expect a == 1;
expect b == D(2,Nil);

}

method M4() {

var D(c, Nil) := D(1, Nil); // OK
assert c == 1;
assert Nil == Nil();
expect c == 1;
expect Nil == Nil();

}

method M6() {

var D(a,D(b,Nil)) := D(1, D(2, Nil)); //OK
assert a == 1;
assert b == 2;
expect a == 1;
expect b == 2;

}

method Main() {
  M1();
  M4();
  M6();
  print "Done\n";
}
