// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype D = D(ghost v:nat)
compiled function p():D { ghost var v:nat :| true; D(v) }

datatype G = G(v:nat)
compiled function q():G { var v:nat :| true; G(v) }

