module ActionsExternsExamples {

  import opened Std.Actions
  import opened Std.ActionsExterns
  import opened Std.BulkActions
  import opened Std.Producers
  import opened Std.Consumers
  import opened Std.Wrappers
  import opened Std.Frames
  import opened Std.Termination

  @IsolateAssertions
  @Test
  method SetIteration() {

    var s: set<nat> := { 1, 2, 3, 4, 5 };
    var e: Producer<nat>, proof := MakeSetReader(s);
    var copy := {};
    while true
      invariant e.Valid()
      invariant fresh(e.Repr)
      invariant copy == Seq.ToSet(e.Produced())
      decreases e.Decreasing()
    {
      ghost var oldOutputs := e.Outputs();
      ghost var oldProduced := e.Produced();
      label before:
      var next := e.Next();
      assert e.Outputs() == oldOutputs + [next];
      ProducedComposition(oldOutputs, [next]);

      proof.ProducesSet(e.history);

      if next.None? {
        assert Seq.Last(e.Outputs()) == None;
        assert e.Done();
        assert Seq.ToSet(e.Produced()) == proof.Set();
        break;
      }
      var x := next.value;

      assert e.Produced() == oldProduced + [x];
      Seq.LemmaNoDuplicatesDecomposition(oldProduced, [x]);
      assert x !in oldProduced;

      copy := copy + {x};
    }

    assert copy == s;
    expect copy == s;
  }

  @Test
  method SetToSeq() {

    var s := { 1, 2, 3, 4, 5 };
    var setReader, producerOfSetProof := MakeSetReader(s);
    assert setReader.Valid();
    var seqWriter := new SeqWriter();
    var writerTotalProof := seqWriter.totalActionProof();
    setReader.ForEach(seqWriter, writerTotalProof);
    var asSeq := seqWriter.values;

    producerOfSetProof.ProducesSet(setReader.history);
    assert Seq.ToSet(asSeq) == s;
    assert Seq.HasNoDuplicates(asSeq);
  }
}