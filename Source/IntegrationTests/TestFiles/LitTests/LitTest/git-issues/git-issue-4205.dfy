// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait T {
  opaque function bar(): int
}

class F extends T {
  opaque function bar(): int {
    1
  }
}