// NONUNIFORM: Rust-specific tests
// RUN: %baredafny run --target=rs --enforce-determinism --type-system-refresh --general-traits=full "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait Super<T> {
  function Compare(a: T, b: T): bool
}

trait Sub<T(==)> extends Super<T> {
  function Compare(a: T, b: T): bool {
    a == b
  }
}

datatype IntOps extends Sub<int> = IntOps {
}

method Main() {
  expect IntOps().Compare(1, 1);
  expect !IntOps().Compare(1, 2);
  print "ok";
}