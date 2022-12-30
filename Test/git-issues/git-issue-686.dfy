// RUN: %baredafny verify %args --relax-definite-assignment "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=js "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=go "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype Color = Blue | Red

function method Foo(c: Color): int {
  match c
  case Blue => 4
  case Blue =>  // warning: redundant branch
    5
  case Red => 6
}

method Moo(c: Color) returns (x: int) {
  match c
  case Blue =>
  case Blue =>  // warning: redundant branch
  case Red =>
}

method Main() {
  var x := Moo(Red);
  print Foo(Red), " ", x, "\n";
}
