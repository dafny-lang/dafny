// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype D = Nil | MM | D(x: int, tail: D)

method M2() {

var D(c, MM()) := D(1, Nil); // ERROR - MM() does not match Nil()
assert c == 1;
assert MM == Nil();

}

method M3() {

var D(c, MM) := D(1, Nil); // ERROR - MM() does not match Nil()
assert c == 1;
assert MM == Nil();

}

method M5() {

var D(a,D(b,MM)) := D(1, D(2, Nil)); // ERROR - MM does not match Nil
assert a == 1;
assert b == 2;

}

