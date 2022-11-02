// RUN: %dafny_0 /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait T {
  predicate {:opaque} True() { true }
}

class C extends T {}