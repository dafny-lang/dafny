// NONUNIFORM: Temporary development of the Rust compiler
// RUN: %baredafny run --target=rs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
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