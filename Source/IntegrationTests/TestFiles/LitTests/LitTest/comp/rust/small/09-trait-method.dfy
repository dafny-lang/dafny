// NONUNIFORM: Rust-specific tests
// RUN: %baredafny run --target=rs --enforce-determinism --emit-uncompilable-code "%s" > "%t"

datatype Super<K, V> = Super

datatype Test<T, O> = Test {
  static const cloud := Super<T,O>.Super
}

method Main() {
}