// RUN: %exits-with 4 %verify --type-system-refresh --check-invariants "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "Baseline.dfy"

module ReadsError refines Baseline {
  class Node<A>... {
    invariant tail.head >= 0 // verification error
  }
}