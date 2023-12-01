// RUN: %exits-with 4 %verify --warn-redundant-assumptions --warn-contradictory-assumptions --show-snippets:true "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M {
  opaque function ToSet(xs: seq<int>): set<int> {
    set x: int | x in xs
  }

  lemma LemmaCardinality(xs: seq<int>)
    ensures |ToSet(xs)| <= |xs|
  {}

  lemma LemmaEmpty(xs: seq<int>)
    requires xs == []
    ensures |ToSet(xs)| == 0
  {
    assume false;
  }
}
