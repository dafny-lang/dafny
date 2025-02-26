// NONUNIFORM: Tests generation of elephant assignment to shadowed variable
// RUN: %baredafny run --target=rs --enforce-determinism "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Option = Some(value: string) | None() {
  function IsFailure(): bool { None? }
  function PropagateFailure(): Option
    requires IsFailure()
  { None() }
  function Extract(): string
    requires !IsFailure()
  { value }
}

function Foo(j: int): Option {
  Some("foo")
}

method Test1(j: int) returns (o: Option) {
  var j :- Foo(j);
  return Some(j);
}

method Test2(j: int) returns (o: Option) {
  var s := "";
  s :- Foo(j);
  return Some(s);
}

method Main() {
  var o := Test1(0);
  expect o == Some("foo");
  o := Test2(0);
  expect o == Some("foo");
}