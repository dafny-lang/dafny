// NONUNIFORM: Rust-specific tests
// RUN: %baredafny run --target=rs --enforce-determinism "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype I8 = x: int | -128 <= x < 128
newtype {:rust_erased false} WrappedI8 = x: int | -128 <= x < 128

method Main() {
  print 0.2, " ", 0.025, " ", -1.5, " ", 1.0 / 3.0, "\n";
  print 3.5.Floor, " ", (-3.5).Floor, " ", |{0.5, 1.0 / 2.0}|, "\n";
  var i: int := 7;
  var i8: I8 := -3;
  // Conversions are exercised with owned operands (assignments) and borrowed ones (print statements)
  var r: real := i as real;
  var n: int := r as int;
  var w: WrappedI8 := r as WrappedI8;
  print r, " ", n, " ", w, " ", i8 as real, "\n";
}
