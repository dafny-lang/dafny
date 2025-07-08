// NONUNIFORM: Rust-specific tests
// RUN: %baredafny run --target=rs --enforce-determinism --type-system-refresh "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %baredafny run --target=rs --enforce-determinism "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype Uint8 = x: int | 0 <= x < 256

datatype Option<T> = Some(value: T) | None {
  predicate IsFailure() {
    None?
  }
  function PropagateFailure<U>(): Option<U> {
    None
  }
  function Extract(): T
    requires !IsFailure() {
    value
  }
  method ExtractMethod() returns (r: T)
    requires !IsFailure() {
    return value;
  }
}

method TestCompile(input: Option<Uint8>) returns (output: Option<Uint8>) {
  var middle :- input;
  var middleMethod := Some(middle).ExtractMethod();
  return None;
}

type CustomBv16 = bv16

method Main() {
  var x: Uint8 := 2;
  // Correct rendering of expressions that can interpret the first '<' as a generic argument
  var y: bv16 := (x as CustomBv16) << 2;
  expect y == 8;
  expect (x as bv16) < 3;
  expect (x as bv16) <= 3;
  print "Everything is ok.";
}