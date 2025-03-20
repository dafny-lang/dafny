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
    twostate predicate ValidOutput(history: seq<((), Box)>, nextInput: (), new nextOutput: Box)
      decreases Repr
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)]) && fresh(nextOutput)
    }
    ghost predicate ValidHistory(history: seq<((), Box)>)
      decreases Repr
    {
      Seq.Map((b: Box) => b.i, OutputsOf(history)) == SeqRange(|history|)
    }

    ghost function Decreases(t: ()): TerminationMetric
      reads Reads(t)
    {
      TMTop
    }

    method Invoke(t: ()) returns (r: Box)
      requires Requires(t)
      reads Repr
      modifies Modifies(t)
      decreases Decreases(t).Ordinal(), 0
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
  class SplitProducer extends Producer<Producer<nat>>, ProducesNewProducersProof<nat> {

    var inputs: seq<nat>

    constructor (inputs: seq<nat>)
      ensures Valid()
      ensures fresh(Repr)
      ensures history == []
    {
      this.inputs := inputs;

      history := [];
      Repr := {this};
      remainingMetric := TMNat(|inputs|);
    }

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases Repr, 0
    {
      && this in Repr
      && ValidHistory(history)
      && remainingMetric == TMNat(|inputs|)
      && (0 < |inputs| ==> Seq.All(Outputs(), IsSome))
    }

    twostate function DumbRepr(new o: Producer<nat>): set<object>
      reads o
    {
      o.Repr
    }

    twostate predicate ValidOutput(history: seq<((), Option<Producer<nat>>)>, nextInput: (), new nextOutput: Option<Producer<nat>>)
      decreases Repr
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)])
    }
    ghost predicate ValidOutputs(outputs: seq<Option<Producer<nat>>>)
      requires Seq.Partitioned(outputs, IsSome)
      decreases Repr
    {
      true
    }

    method Invoke(t: ()) returns (result: Option<Producer<nat>>)
      requires Requires(t)
      reads Repr
      modifies Modifies(t)
      decreases Decreases(t).Ordinal(), 0
      ensures Ensures(t, result)
      ensures if result.Some? then
                old(remainingMetric).DecreasesTo(remainingMetric)
              else
                old(remainingMetric) == remainingMetric
    {
      if inputs == [] {
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

      remainingMetric := TMNat(|inputs|);
      reveal TerminationMetric.DecreasesTo();
    }

    ghost function Producer(): Producer<Producer<nat>> {
      this
    }

    // TODO: Depends on figuring out the reads clause issues with ValidOutput
    twostate lemma {:axiom} ProducedAllNew(new produced: Producer<nat>)
      requires old(Action().Valid())
      requires Action().ValidOutput(old(Action().history), (), Some(produced))
      ensures produced.Valid()
      ensures fresh(produced.Repr)
      ensures Producer().Repr !! produced.Repr
      ensures produced.history == []
  }

  @IsolateAssertions
  method {:test} ExamplePipeline() {
    var producerProducer := new SplitProducer([1, 2, 3, 4, 5]);

    var flattened := new FlattenedProducer(producerProducer, producerProducer);

    var collector := new SeqWriter();

    var collectorTotalProof := new DefaultTotalActionProof(collector);
    flattened.ForEachRemaining(collector, collectorTotalProof);

    expect collector.values == [0, 1, 1, 1, 1, 2, 2, 2, 2, 3], collector.values;
  }
}