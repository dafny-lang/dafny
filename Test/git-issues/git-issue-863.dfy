// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype D = D(ghost v:nat)
function p():D { ghost var v:nat :| true; D(v) }

datatype G = G(v:nat)
function q():G { var v:nat :| true; G(v) }

