// RUN: %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module A {
  opaque predicate Valid<R>(n: int)
  { true }
}

abstract module B refines A {
}