// RUN: %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The axiom for membership in the items of a map, and of an imap, did not say that an
// item is a pair, so it admitted other values as items too. Every item a program can
// name is a genuine pair, so no program is known to prove false by this; the axioms
// themselves had no model (see the issue). What a program can see is that facts about
// the items of a map, such as these, now verify; they did not before.

method MapItems() {
  assert map[1 := 2].Items == {(1, 2)};
}

method IMapItems() {
  assert imap[1 := 2].Items == iset{(1, 2)};
}
