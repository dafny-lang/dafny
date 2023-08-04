// RUN: %dafny /compile:0 /noVerify /print:%t.bpl "%s"
// RUN: %boogie "%t.bpl" > "%t"
// RUN: %diff "%s.expect" "%t"

function Test(f: (int ~> bool)): (b:bool) reads f.reads { true }