// NONUNIFORM: Rust-specific test for nested set comprehensions type inference
// RUN: %baredafny run --target=rs --enforce-determinism "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const SomeMaps := {map["a" := "b"]}
const OhNo := set x <- (set m <- SomeMaps :: m) :: x

method Main() {
    print OhNo, "\n";
}
