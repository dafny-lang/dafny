// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function F<A>(l: seq<A>): bool {
  forall i :: 0 <= i < |l|-1 ==> l[i] == l[i + 1] || l[i] == l[i + 1]
}

