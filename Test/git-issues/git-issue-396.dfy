// RUN: %baredafny run %args --target=cs "%s" > "%t"
// RUN: %baredafny run %args --target=js "%s" >> "%t"
// RUN: %baredafny run %args --target=go "%s" >> "%t"
// RUN: %baredafny run %args --target=java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype Foo = Bar(value: int)

method GetValue(f: Foo) returns (i: int) {
  match f
  case Bar(Bar) =>
    return 72 + Bar;
}

method Main() {
  var x: int := 0;
  var f: Foo := Bar(42);
  x := GetValue(f);
  print x, "\n";
}
