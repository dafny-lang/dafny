// RUN: %exits-with 4 %verify --referrers --type-system-refresh "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Companion to git-issue-6378.dfy, which reaches the crash through the trigger the extreme-predicate
// machinery builds. A memory location over a non-reference collection is desugared into a set
// comprehension carrying its own resolver-generated {:trigger}, so the same clone path is reached
// from a second, unrelated place.
//
// MemoryLocationSetComprehension has two call sites and each needs its own case: a field location
// (`s`x`) and an index location (`s`[0]`). Both crash on master; no other test reaches either.
// The two IsResolverGenerated flags in that helper are inert on today's corpus -- removing both
// leaves 100 git-issues files byte-identical -- so these cases pin the crash, not the flags.

abstract module A {
  class Test { var x: int }
  predicate P(z: int)

  method FieldLocation(s: set<Test>)
    modifies s`x
  {
    var z :| P(z);
  }

  method IndexLocation(s: set<array<int>>)
    modifies s`[0]
    requires forall a <- s :: a.Length > 0
  {
    var z :| P(z);
  }
}

module B refines A {
  predicate P(z: int) { z > 0 }
}
