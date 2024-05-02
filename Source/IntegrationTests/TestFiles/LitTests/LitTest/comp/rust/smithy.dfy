// NONUNIFORM: Test of the output of the Rust translation
// RUN: %baredafny run --target=rs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %OutputCheck --file-to-check "%S/smithy-rust/src/smithy.rs" "%S/smithy.check"

module Submodule {
}

method DoesNotRequireEquality<T>(x: T, y: T) {
  print "And that's ok.\n";
}

method RequiresEquality<T(==)>(x: T, y: T) {
  print "x == y ? ", x == y, "\n";
  DoesNotRequireEquality<T>(x, y);
}

method Main() {
  var zero: nat := 0;
  var one: nat := 1;
  RequiresEquality(one, one);
  print "Hello", one, "\n";
}