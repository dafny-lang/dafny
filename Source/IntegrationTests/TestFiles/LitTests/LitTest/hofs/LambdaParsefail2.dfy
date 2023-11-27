// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"



method Fail2() {
    var g4 := (x, y : A) => (y, x : B); // RHS should fail!
}

