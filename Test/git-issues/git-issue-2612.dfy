// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait T {
  predicate {:opaque} True() { true }
}

class C extends T {}
