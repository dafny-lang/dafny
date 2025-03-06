// NONUNIFORM: Rust-specific tests
// RUN: %baredafny run --target=rs --enforce-determinism --type-system-refresh --general-traits=full "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// UNSUPPORTED: windows

trait Super<T> {
  function Compare(a: T, b: T, c: bool): bool
    decreases a
}

datatype BoolOps extends Super<bool> = BoolOps {
  function Compare(a: bool, b: bool, c: bool): bool {
    a == b
  }
}

method Main() {
  expect BoolOps().Compare(true, true, true);
  expect !BoolOps().Compare(true, false, true);
  print "ok";
}