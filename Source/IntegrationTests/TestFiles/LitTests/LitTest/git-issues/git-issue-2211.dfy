// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate P1(a: int)
predicate P2(a: int)

predicate Q(s: seq<int>) {
  forall i | 0 <= i < |s| ::
    && P1(s[i])
    && P2(s[i])
}

method M(s: seq<int>)
  requires forall i | 0 <= i < |s| :: P1(s[i])
  // requires forall i | 0 <= i < |s| :: P2(s[i])
  ensures Q(s)
{}