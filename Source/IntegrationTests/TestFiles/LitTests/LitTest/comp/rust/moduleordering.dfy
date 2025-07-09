// NONUNIFORM: Test of the Rust compiler to ensure it emits modules in a deterministic order.
// RUN: %baredafny translate rs --enforce-determinism "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%S/moduleordering-rust/src/moduleordering.rs" "%s"
// CHECK-L: pub mod A {
// CHECK-L: pub mod B {
// CHECK-L: pub mod C {
// CHECK-L: pub mod D {
// CHECK-L: pub mod E {
// CHECK-L: pub mod F {
// CHECK-L: pub mod G {
// CHECK-L: pub mod H {

module B { const X := "B" }
module D { import B const X := B.X }
module C { import A const X := A.X }
module E { import C const X := C.X }
module A { import G const X := G.X }
module G { const X := "G" }
module F { const X := "F" }
module H { const X := "H" }