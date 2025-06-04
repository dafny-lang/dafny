// RUN: %verify --type-system-refresh --verify-invariants "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait T extends object { var y: int }

class Node<A> extends T {
  var head: int
  var tail: Node?<A>
  invariant head >= 0 && tail != null // OK
}