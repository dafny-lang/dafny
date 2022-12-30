// RUN: %baredafny verify %args "%s" > "%t"
// RUN: ! %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: ! %baredafny run %args --no-verify --target=go "%s" >> "%t"
// RUN: ! %baredafny run %args --no-verify --target=java "%s" >> "%t"
// RUN: ! %baredafny run %args --no-verify --target=js "%s" >> "%t"
// RUN: ! %baredafny run %args --no-verify --target=py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype Option<T> = None | Some(get: T)

method Main() {
  var x := Some("where over the rainbow");
  expect x.None?, x;
}
