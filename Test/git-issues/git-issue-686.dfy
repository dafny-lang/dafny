// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
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
