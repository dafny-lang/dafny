// RUN: %exits-with 4 %verify --type-system-refresh --check-invariants "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait T extends object {
  predicate P() reads this { assert this.invariant(); false }
  invariant P()
}

class C extends T {
  constructor() {}
}