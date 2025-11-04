// RUN: %verify --type-system-refresh --check-invariants "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Baseline {
  trait T extends object { var y: int }
  
  // Dummy type parameter to make sure Boogie generator doesn't trip up
  class Node<A> extends T {
    var head: int
    var tail: Node?<A>
    invariant head >= 0 && tail != null // OK
    constructor() {
      head := 0;
      tail := this;
    }
  }
}