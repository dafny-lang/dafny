// RUN: %dafny_0 /print:"%t.print" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


method Fail2() {
    var g4 := (x, y : A) => (y, x : B); // RHS should fail!
}

