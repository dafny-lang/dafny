// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment

datatype Color = Blue | Red

function Foo(c: Color): int {
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
