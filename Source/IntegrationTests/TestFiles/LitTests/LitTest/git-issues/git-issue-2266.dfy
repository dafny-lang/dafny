// RUN: %verify --bprint "%t.bpl" "%s"
// RUN: %boogie "%t.bpl" > "%t"
// RUN: %diff "%s.expect" "%t"

function Test(f: (int ~> bool)): (b:bool) requires forall x: int :: f.requires(x) reads f.reads { true }
