// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


datatype D = D(ghost v:nat)
function p():D { ghost var v:nat :| true; D(v) }

datatype G = G(v:nat)
function q():G { var v:nat :| true; G(v) }

