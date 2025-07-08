// NONUNIFORM: Test of the Dafny-to-Rust tests
// RUN: %baredafny test --target=rs --enforce-determinism "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %baredafny build --compile-suffix --target=rs --enforce-determinism "%s" > "%t"
// RUN: "%S/tests-rust/cargo" run -- Hello > "%t"
// RUN: %diff "%s.main.expect" "%t"

method {:test} TestIfTestsAreWorking() {
  expect 1 == 1, "Ok";
}

module WrappedTests {
  method {:test} TestIfTestsAreWorking() {
    expect 1 == 1, "Ok";
  }
  method Main(args: seq<string>) {
    print "Detected main\n";
    if |args| > 1 {
      print args[1];
    }
  }
}
