// RUN: %exits-with 2 %resolve --type-system-refresh --check-invariants "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C {
  predicate P() reads this { false }
  invariant P()
}