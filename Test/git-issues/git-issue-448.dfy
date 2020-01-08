// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C {
  var u: int
  method M() {
  }
  function method F(): int {
    5
  }
}

codatatype Stream = More(x: int, tail: Stream)

method Main() {
  var c: C;
  var s: Stream;
  print s.x, "\n";  // error: "s" hasn't been initialized yet
  if * {
    // Regression test:
    c.M();  // error: "c" hasn't been initialized yet
  } else if * {
    var f := c.F();  // error: "c" hasn't been initialized yet
  } else if * {
    P(c);  // error: "c" hasn't been initialized yet
  } else if * {
    var u := c.u;  // error: "c" hasn't been initialized yet
  } else {
    // Regression test:
    (if 3 / 0 < 7 then c else c).M();  // error: division by zero
  }
}

method P(w: C) {
  w.M();
}
