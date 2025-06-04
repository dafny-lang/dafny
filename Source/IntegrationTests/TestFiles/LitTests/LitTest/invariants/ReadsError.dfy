// RUN: %verify --type-system-refresh --verify-invariants "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "Baseline.dfy"

class Node<A>... {
  invariant tail.head >= 0 // verification error
}