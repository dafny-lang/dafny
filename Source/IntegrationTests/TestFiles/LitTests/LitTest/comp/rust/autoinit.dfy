// NONUNIFORM: Can't create class instances without constructors as Rust does not support Dafny defaults since subset types are erased
// RUN: %exits-with 2 %baredafny run %args --enforce-determinism --target=rs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Test<T(0)> {
  var x: T
}

type Positive = x: int | x > 0 witness 1

method Main() {
  var x: Test := new Test<Positive>;
  print x.x, "\n";
  if x.x == 0 {
    assert false;
    expect false;
  }
  x.x := 2;
  expect x.x == 2;
}

