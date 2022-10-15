// RUN: %dafny_0 /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

lemma Lemma(x: int, p: multiset<int>)
  requires x in p
{}

method Test() {
  Lemma(1, multiset{});
}