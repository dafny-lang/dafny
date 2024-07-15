// NONUNIFORM: Demonstration of the use of the external Rust Option<> type
// RUN: %baredafny test --target=rs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method {:test} TestIfTestsAreWorking() {
  expect 1 == 1, "Ok";
}