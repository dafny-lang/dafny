// RUN: %exits-with 4 %dafny /compile:0 /rprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost function F(l: seq<bool>, x: bool, js: seq<int>): bool {
  forall i, j :: js[i] < j < js[i + 1] ==> l[j] == x
}
