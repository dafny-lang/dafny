// RUN: %baredafny verify %args --disable-nonlinear-arithmetic "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module One {
  type State
  type Action

  predicate StateNext(s:State, s':State, a:Action)

  predicate StateNextSeq(sseq:seq<State>, actions:seq<Action>)
  {
    |sseq| == |actions| + 1
    && (forall i :: 0 <= i < |actions| ==> StateNext(sseq[i], sseq[i+1], actions[i]))
  }

}

abstract module Two {
    import opened O : One
}
