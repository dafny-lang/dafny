// RUN: %verify --type-system-refresh --check-invariants "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait Poly<A(!new)> {
  var a: A
  invariant a == a
}