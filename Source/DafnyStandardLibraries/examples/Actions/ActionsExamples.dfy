module ActionsExamples {
  import opened Std.Actions
  import opened Std.Producers
  import opened Std.Consumers
  import opened Std.Wrappers
  import opened Std.Frames
  import opened Std.Termination

  // Demonstrating the simplest idiom
  // for looping over the values produced by a Producer<T>
  method {:test} SimpleProducerLoop() {
    var p := MakeProducer();
    while true
      invariant p.Valid()
      invariant fresh(p.Repr)
      decreases p.Remaining()
    {
      var next := p.Next();
      if next.None? {
        break;
      }

      expect 0 < next.value <= 5;
    }
  }

  method MakeProducer() returns (p: Producer<nat>)
    ensures p.Valid()
    ensures fresh(p.Repr)
  {
    p := new SeqReader([1, 2, 3, 4, 5]);
  }

  // Demonstration that actions can consume/produce reference values as well,
  // despite the usual challenges of quantifying over such types.

  class Box {
    const i: nat

    constructor(i: nat)
      ensures this.i == i
      reads {}
    {
      this.i := i;
    }
  }

  function SeqRange(n: nat): seq<nat> {
    seq(n, i => i)
  }

  lemma SeqRangeIncr(prefix: seq<nat>, n: nat)
    requires prefix == SeqRange(n)
    ensures prefix + [n] == SeqRange(n + 1)
  {}

  @AssumeCrossModuleTermination
  class BoxEnumerator extends Action<(), Box> {

    var nextValue: nat

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases Repr, 0
    {
      && this in Repr
      && ValidHistory(history)
      && nextValue == |history|
    }

    constructor ()
      ensures Valid()
      ensures fresh(Repr)
      ensures history == []
    {
      nextValue := 0;
      history := [];
      Repr := {this};
    }

    ghost predicate ValidInput(history: seq<((), Box)>, next: ())
      requires ValidHistory(history)
      decreases Repr
    {
      true
    }
    ghost predicate ValidHistory(history: seq<((), Box)>)
      decreases Repr
    {
      Seq.Map((b: Box) => b.i, OutputsOf(history)) == SeqRange(|history|)
    }

    ghost function Decreases(t: ()): ORDINAL
      reads Reads(t)
    {
      ReprTerminationMetric().Ordinal()
    }

    method Invoke(t: ()) returns (r: Box)
      requires Requires(t)
      reads Repr
      modifies Modifies(t)
      decreases Decreases(t), 0
      ensures Ensures(t, r)
    {
      assert Requires(t);
      ghost var producedBefore := Outputs();

      r := new Box(nextValue);
      UpdateHistory(t, r);
      Repr := {this};
      nextValue := nextValue + 1;

      SeqRangeIncr(Seq.Map((b: Box) => b.i, producedBefore), |producedBefore|);
      assert Valid();
    }
  }

  method BoxEnumeratorExample() {
    var enum: BoxEnumerator := new BoxEnumerator();
    assert |enum.Outputs()| == 0;
    var a := enum.Invoke(());

    assert enum.Outputs() == [a];
  }

  @IsolateAssertions
  @ResourceLimit("10e6")
  method ConsumerExample() {
    var a: DynamicArrayWriter<nat> := new DynamicArrayWriter();
    var _ := a.Invoke(1);
    var _ := a.Invoke(2);
    var _ := a.Invoke(3);
    var _ := a.Invoke(4);
    var _ := a.Invoke(5);
    assert a.Inputs() == [1, 2, 3, 4, 5];
    assert a.storage.items == [1, 2, 3, 4, 5];
  }

  @AssumeCrossModuleTermination
  class SplitProducer extends ProducerOfNewProducers<nat> {

    var inputs: seq<nat>

    constructor (inputs: seq<nat>)
      ensures Valid()
      ensures fresh(Repr)
      ensures history == []
    {
      this.inputs := inputs;

      history := [];
      Repr := {this};
    }

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases Repr, 0
    {
      && this in Repr
      && ValidHistory(history)
      && (0 < |inputs| ==> Seq.All(Outputs(), IsSome))
    }

    ghost predicate ValidOutputs(outputs: seq<Option<Producer<nat>>>)
      requires Seq.Partitioned(outputs, IsSome)
      decreases Repr
    {
      true
    }

    ghost function MaxProduced(): TerminationMetric
      ensures MaxProduced().Valid()
    {
      TMTop
    }

    ghost function RemainingMetric(): TerminationMetric
      requires Valid()
      reads this, Repr
      decreases Repr, 3
      ensures RemainingMetric().Valid()
    {
      TMNat(|inputs|)
    }

    method Invoke(t: ()) returns (result: Option<Producer<nat>>)
      requires Requires(t)
      reads Repr
      modifies Modifies(t)
      decreases Decreases(t), 0
      ensures Ensures(t, result)
      ensures if result.Some? then
                old(Remaining()) > Remaining()
              else
                old(Remaining()) >= Remaining()
      ensures result.Some? ==> JustProduced(result.value)
    {
      assert Valid();

      if |inputs| == 0 {
        result := None;

        OutputsPartitionedAfterOutputtingNone();
        ProduceNone();
      } else {
        var x := inputs[0];
        inputs := Seq.DropFirst(inputs);
        var p := new SeqReader([x / 2, x - (x / 2)]);

        result := Some(p);

        OutputsPartitionedAfterOutputtingSome(result.value);
        ProduceSome(result.value);
      }

      reveal TerminationMetric.Ordinal();
      assert Valid();
    }
  }

  @IsolateAssertions
  method {:test} ExamplePipeline() {
    var producerProducer := new SplitProducer([1, 2, 3, 4, 5]);

    var flattened := new FlattenedProducer(producerProducer);

    var collector := new SeqWriter();

    var collectorTotalProof := new DefaultTotalActionProof(collector);
    flattened.ForEachRemaining(collector, collectorTotalProof);

    expect collector.values == [0, 1, 1, 1, 1, 2, 2, 2, 2, 3], collector.values;
  }
}