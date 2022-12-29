// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=js "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=go "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// Regression: A constructor like PushOp with 1+ ghost parameters and 0 non-ghost parameters
// once caused the Java compiler to emit two 0-parameter constructors

datatype Op =
  | NoOp
  | PushOp(ghost id: int)

method Main() {
  var o := PushOp(20);
  print o, "\n";
}
