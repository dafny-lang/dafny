// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate P1(a: int)
predicate P2(a: int)
predicate P3(a: int)

predicate Q(s: seq<int>) {
  exists i | 0 <= i < |s| ::
    || P1(s[i])
    || P2(s[i])
}

method M(s: seq<int>)
  requires exists i | 0 <= i < |s| :: P1(s[i]) || P2(s[i]) || P3(s[i])
  // requires exists i | 0 <= i < |s| :: P2(s[i])
  ensures Q(s)
{}