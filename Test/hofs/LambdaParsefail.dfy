// RUN: %dafny /compile:0 /print:"%t.print" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Fails() {
    var g1 := x.x => x;   // fail
    var g2 := x() => x;   // fail
    var g3 := ((x)) => x; // fail

}

method Fail() {
    var g8 := x : int => x;   // not ok!
}

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
