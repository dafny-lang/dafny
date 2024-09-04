// NONUNIFORM: Rust-specific tests
// RUN: %baredafny translate rs --rust-module-name namewrapper "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%S/custommodule-rust/src/custommodule.rs" "%S/custommodule.check"

module EnclosingModule {
  method Print() {
    print "hello\n";
  }
}

method Test() {
  EnclosingModule.Print();
}