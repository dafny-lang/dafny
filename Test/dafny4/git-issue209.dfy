// RUN: %dafny /compile:0 /rprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function F(l: seq<bool>, x: bool, is: seq<int>): bool {
  forall i, j :: is[i] < j < is[i + 1] ==> l[j] == x
}
