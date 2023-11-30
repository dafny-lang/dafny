// RUN: %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait T {
  opaque function bar(): (r: int)
}

class F extends T {
  constructor() {}
  opaque function bar(): (r: int) {
    1
  }
}