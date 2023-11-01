// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


ghost function F(l: seq<bool>, x: bool, js: seq<int>): bool {
  forall i, j :: js[i] < j < js[i + 1] ==> l[j] == x
}
