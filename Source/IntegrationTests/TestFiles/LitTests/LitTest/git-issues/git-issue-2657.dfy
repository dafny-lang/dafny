// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


lemma Lemma(x: int, p: multiset<int>)
  requires x in p
{}

method Test() {
  Lemma(1, multiset{});
}