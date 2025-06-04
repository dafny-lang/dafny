// RUN: %resolve --type-system-refresh "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "Baseline.dfy"

class Node<A>... {
  invariant y >= 0 // resolution error
}