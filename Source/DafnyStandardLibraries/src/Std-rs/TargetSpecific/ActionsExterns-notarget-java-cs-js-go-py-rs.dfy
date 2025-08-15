replaceable module Std.ActionsExterns {

  import opened Producers

  method MakeSetReader<T>(s: set<T>) returns (p: Producer<T>, ghost proof: ProducerOfSetProof<T>)
    ensures p.Valid()
    ensures fresh(p.Repr)
    ensures p.history == []
    ensures proof.Producer() == p
    ensures proof.Set() == s

}