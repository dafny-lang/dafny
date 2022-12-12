// RUN: %exits-with 2 %dafny /print:"%t.print" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Fails() { // all these fail
    var g1 := x.x => x;
    var g2 := x() => x;
    var g3 := ((x)) => x;
    var g4 := _a => 5;
    var g5 := x : int => x;
}

// the rest of these are OK:

function f():() {
  a.b(x); a.b(x)
}

method M() {
  g := a.b(x);
}

method M() {
  g := y => a(y);
}

method M() {
  g := y => a.b(y);
}

function f():() {
  (u => a.b(x); a(x))(); a(x)
}
