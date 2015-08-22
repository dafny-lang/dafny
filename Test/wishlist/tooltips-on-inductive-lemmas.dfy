// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /autoTriggers:1 /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

inductive lemma P()
  requires Q() { // WISH the tooltip for this was broken at some point between
                 // revisions 94ee216fe0cd (1179) and bd779dda3b3d (1785)
  P();
}

inductive predicate Q() {
  Q()
}
