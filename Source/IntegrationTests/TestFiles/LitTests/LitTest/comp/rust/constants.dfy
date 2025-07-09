// NONUNIFORM: Tests that references to function constants are eta-expanded with an additional call and type annotations in Rust backend
// RUN: %baredafny run --target=rs --enforce-determinism "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const f: int -> int := x => x
const g: int -> int := f
