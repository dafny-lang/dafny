// NONUNIFORM: Test of cargo test to support Dafny tests
// RUN: %baredafny build --target=rs "%s" > "%t"
// RUN: %exits-with 101 "%S/cargotest-rust/cargo" test >> "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK: test Tests::TestFail1 ... FAILED
// CHECK: test Tests::TestFail2 ... FAILED
// CHECK: test Tests::TestSucceed3 ... ok
// RUN: %OutputCheck --file-to-check "%S/cargotest-rust/src/cargotest.rs" "%S/cargotestoutput.check"

module {:test} Tests {
  method {:test} TestFail1() {
    expect true == false;
  }

  method {:test} TestFail2() {
    expect false == true;
  }

  method {:test} TestSucceed3() {
    expect true == true;
  }
}