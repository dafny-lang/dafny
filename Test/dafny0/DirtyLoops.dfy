// RUN: %dafny /compile:0 /dprint:"%t.dprint.dfy" "%s" > "%t"; %dafny /noVerify /compile:0 "%t.dprint.dfy" >> "%t"
// RUN: %diff "%s.expect" "%t"

method M(S: set<int>) {
  forall s | s in S ensures s < 0;
}
