// RUN: %baredafny translate rs %args "%s"
// RUN: %OutputCheck --file-to-check "%S/classes-rust/src/classes.rs" "%s"
// CHECK: y: .*MaybeUninit
// RUN: %baredafny run --target=rs > "%t"
// RUN: %diff "%s.expect" "%t"

class Y {
  var c: int
}
class X {
  var y: Y
  constructor() {
    y := new Y;
    new;
    y.c := 0;
  }
}
method Main() {
  var x := new X();
  print x.y.c;
}