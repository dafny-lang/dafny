// RUN: %exits-with 2 %resolve --type-system-refresh "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "Baseline.dfy"

module InheritedMemberError refines Baseline {
  class Node<A>... {
    invariant y >= 0 // resolution error
  }
}