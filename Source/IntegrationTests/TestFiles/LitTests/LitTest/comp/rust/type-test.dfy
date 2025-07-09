// NONUNIFORM: Tests that type tests work in the Rust backend
// RUN: %baredafny run --target=rs --general-traits=legacy --enforce-determinism "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %baredafny run --target=rs --general-traits=legacy --enforce-determinism --raw-pointers "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait T { }
class A extends T { constructor() {} }
class B extends T { }

method Main() {
  var v: T := new A();
  expect !(v is B), "v shouldn't be B";
  expect v is A, "v should be A";
}
