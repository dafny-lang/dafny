// RUN: %testDafnyForEachResolver "%s"


ghost function F<A>(l: seq<A>): bool {
  forall i :: 0 <= i < |l|-1 ==> l[i] == l[i + 1] || l[i] == l[i + 1]
}

