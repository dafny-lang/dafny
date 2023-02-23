// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait T {
  ghost predicate {:opaque} True() { true }
}

class C extends T {}
