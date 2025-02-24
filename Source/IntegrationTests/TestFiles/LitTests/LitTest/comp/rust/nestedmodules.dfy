// NONUNIFORM: Rust-specific tests
// RUN: %baredafny run --target=rs --enforce-determinism "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Checks that, despite module B being prefixed with A, there will be a "mod B" somewhere
// and not an encoding like "mod A_B".
// This module will automatically be in mod A and referred to as "A::B"
// RUN: %OutputCheck --file-to-check "%S/nestedmodules-rust/src/nestedmodules.rs" "%S/nestedmodules.check"

module A.B {
  import opened C
  method Test() {
    print "A.B.Test-";
    Bar();
  }
}

module A {
  import opened B
  module B.C {
    method Bar() {
      print "A.B.C.Bar-";
    }
  }

  method Foo() {
    print "A.Foo-";
    Test();
    B.C.Bar();
  }
}

method Main() {
  print "main-";
  A.Foo();
  print "end";
}