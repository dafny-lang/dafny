// RUN: %verify "%s" > "%t"
// RUN: ! %run --no-verify --target cs "%s" >> "%t"
// RUN: ! %run --no-verify --target go "%s" >> "%t"
// RUN: ! %run --no-verify --target java "%s" >> "%t"
// RUN: ! %run --no-verify --target js "%s" >> "%t"
// RUN: ! %run --no-verify --target py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype Option<T> = None | Some(get: T)

method Main() {
  var x := Some("where over the rainbow");
  expect x.None?, x;
}
