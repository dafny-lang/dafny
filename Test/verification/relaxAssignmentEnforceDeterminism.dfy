// RUN: %baredafny build %args --relax-definite-assignment --enforce-determinism "%s" > "%t" || true
// RUN: %diff "%s.expect" "%t"

method Foo() {
}
