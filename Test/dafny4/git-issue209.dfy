// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function F(l: seq<bool>, x: bool, js: seq<int>): bool {
  forall i, j :: js[i] < j < js[i + 1] ==> l[j] == x
}
