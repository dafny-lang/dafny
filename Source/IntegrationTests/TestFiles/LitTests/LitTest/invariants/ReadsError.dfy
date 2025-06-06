// RUN: %exits-with 4 %verify --type-system-refresh --verify-invariants "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "Baseline.dfy"

module ReadsError refines Baseline {
  class Node<A>... {
    invariant tail != null // TODO should be visible from refined module
    invariant tail.head >= 0 // verification error
  }
}