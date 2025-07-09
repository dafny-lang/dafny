// NONUNIFORM: Test of cargo test to support Dafny tests
// RUN: %baredafny build --target=rs "%s" --enforce-determinism > "%t"
// RUN: %exits-with 101 "%S/cargotest-rust/cargo" test >> "%t"
// RUN: %OutputCheck --file-to-check "%t" "%S/cargotest1.check"
// RUN: %OutputCheck --file-to-check "%t" "%S/cargotest2.check"
// RUN: %OutputCheck --file-to-check "%t" "%S/cargotest3.check"
// RUN: %OutputCheck --file-to-check "%S/cargotest-rust/src/cargotest.rs" "%S/cargotestoutput.check"

module {:rust_cfg_test} Tests {
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