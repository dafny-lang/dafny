// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


method Fails() { // all these fail
    var g1 := x.x => x;
    var g2 := x() => x;
    var g3 := ((x)) => x;
    var g4 := _a => 5;
    var g5 := x : int => x;
}

// the rest of these are OK:

ghost function f():() {
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

ghost function f():() {
  (u => a.b(x); a(x))(); a(x)
}
