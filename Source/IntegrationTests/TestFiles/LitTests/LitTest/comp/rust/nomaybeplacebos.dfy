// NONUNIFORM: Test of the output of the Rust translation
// RUN: %baredafny translate rs "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%S/nomaybeplacebos-rust/src/nomaybeplacebos.rs" "%S/nomaybeplacebos.check"


method Test(i: int) returns (j: int) {
  j := i;
}

method Main() {
  var j := Test(1);
  var k := Test(j);
}