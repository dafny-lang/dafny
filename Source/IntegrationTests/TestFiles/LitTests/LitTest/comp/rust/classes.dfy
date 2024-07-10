// NONUNIFORM: Temporary development of the Rust compiler
// RUN: %baredafny run --target=rs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %baredafny run --target=rs --raw-pointers "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Y {
  var c: int
  ghost var Repr: set<object>
  constructor(c: int) ensures this.c == c {
    this.c := c;
    this.Repr := {this};
  }

  constructor Two() ensures c == 2 {
    this.c := 2;
    this.Repr := {this};
  }
}

datatype FunWrap<!T, +R> = FunWrap(
  fn: int -> Tuple2<T, R>)

datatype Tuple2<+A, +B> = Tuple2(A, B)
method Main() {
  var x := new Y(3);
  var y := new Y.Two();
  expect x.c == 3;
  expect y.c == 2;
  var z := ([1], [2]);
  var w := z.0;
  var fw := FunWrap<Y, Y>.FunWrap((z: int) => Tuple2(x, y));
  var fx: FunWrap<Y, object> := fw;
  print "Everything is ok.";
}