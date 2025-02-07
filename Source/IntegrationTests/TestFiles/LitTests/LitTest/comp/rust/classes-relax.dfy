// NONUNIFORM: Rust does not support relaxed definite assignment
// RUN: %exits-with 3 %baredafny run --target=rs "%s" > "%t"
// RUN: %diff "%s.wrong.expect" "%t"
// RUN: %baredafny run --target=rs --enforce-determinism "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype D = D(value: int)

class Y {
  var c: int
  const d: D
  constructor(c: int) ensures this.c == c && d.value == c {
    this.c := c;
    if c == 1 {
      this.d := D(1);
    } else {
      this.d := D(c);
    }
  }

  constructor Two(c: int, b: bool) ensures this.c == c && d.value == c
    requires b
  {
    this.c := c; // d not assigned, compilation error.
    if b {
      this.d := D(c);
    }
    // This will emit a conditional panick but Dafny will prove it's unreachable
  }
}

method Main() {
  var y := new Y(1);
  var y2 := new Y.Two(1, true);
  print "Instantiation successful";
}