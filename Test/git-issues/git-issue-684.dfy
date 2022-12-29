// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=js "%s" >> "%t"
// RUN: %exits-with 3 %baredafny run %args --no-verify --target=go "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype Level1 = Level1(u:int)
datatype Level2 = Level2(u:int, l:Level1)

method TestNestedLet() {
  var x := Level2(5, Level1(3));

  var Level2(u, Level1(v)) := x;
}

