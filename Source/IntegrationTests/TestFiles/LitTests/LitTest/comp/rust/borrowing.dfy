// NONUNIFORM: Rust-specific tests
// RUN: %baredafny run --target=rs --emit-uncompilable-code --enforce-determinism "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype U8 = x: int | 0 <= x <= 255

datatype Test = Test() {
  predicate At(x: U8) {
    true
  }
}

/* Converts a sequence to a set. */
function {:opaque} ToSet<T>(xs: seq<T>): set<T>
{
  set x: T | x in xs
}

method Main() {
  var z := Test().At(0);
  var x := ["abc", "def", "abc"];
  var w := ToSet(x);
  expect |w| == 2;
}