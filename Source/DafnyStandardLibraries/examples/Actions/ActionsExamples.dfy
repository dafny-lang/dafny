module ActionsExamples {
  import opened Std.Actions
  import opened Std.Producers
  import opened Std.Consumers
  import opened Std.Wrappers
  import opened Std.Frames

  // Demonstrating the simplest idiom
  // for looping over the values produced by a Producer<T>
  method SimpleProducerLoop() {
    var p := MakeProducer();
    while true 
      invariant p.Valid()
      invariant fresh(p.Repr)
      decreases p.remaining.Ordinal()
    {
      var next := p.Next();
      if next.None? {
        break;
      }

      expect 0 <= next.value < 5;
    }
  }

  method MakeProducer() returns (p: Producer<nat>)
    ensures p.Valid()
    ensures fresh(p.Repr)
  {
    p := new SeqProducer([1, 2, 3, 4, 5]);
  }

  // Demonstration that actions can consume/produce reference values as well,
  // despite the usual challenges of quantifying over such types.

  class Box {
    const i: nat

    constructor(i: nat)
      ensures this.i == i
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
      decreases height, 0
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
      height := 1;
    }

    ghost predicate ValidInput(history: seq<((), Box)>, next: ())
      requires ValidHistory(history)
      decreases height
    {
      true
    }
    twostate predicate ValidOutput(history: seq<((), Box)>, nextInput: (), new nextOutput: Box)
      decreases height
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)]) && fresh(nextOutput)
    }
    ghost predicate ValidHistory(history: seq<((), Box)>)
      decreases height
    {
      Seq.Map((b: Box) => b.i, OutputsOf(history)) == SeqRange(|history|)
    }

    method Invoke(t: ()) returns (r: Box)
      requires Requires(t)
      reads Repr
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
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

  method {:rlimit 0} BoxEnumeratorExample() {
    var enum: BoxEnumerator := new BoxEnumerator();
    assert |enum.Outputs()| == 0;
    var a := enum.Invoke(());

    assert enum.Outputs() == [a];
    // assert Seq.Map((b: Box) => b.i, enum.Outputs()) == SeqRange(1) == [0];
    // assert a.i == 0;

    // var b := enum.Invoke(());
    // var c := enum.Invoke(());
    // var d := enum.Invoke(());
    // var e := enum.Invoke(());
  }

  method {:rlimit 0} ConsumerExample() {
    var a: DynamicArrayConsumer<nat> := new DynamicArrayConsumer();
    var _ := a.Invoke(1);
    var _ := a.Invoke(2);
    var _ := a.Invoke(3);
    var _ := a.Invoke(4);
    var _ := a.Invoke(5);
    var _ := a.Invoke(6);
    assert a.Inputs() == [1, 2, 3, 4, 5, 6];
    assert a.storage.items == [1, 2, 3, 4, 5, 6];
  }

  @AssumeCrossModuleTermination
  class SplitAction extends Action<nat, Producer<nat>>, OutputsFreshProof<nat> {

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases height, 0
    {
      && this in Repr
      && ValidHistory(history)
    }

    constructor ()
      ensures Valid()
      ensures fresh(Repr)
      ensures history == []
    {
      history := [];
      Repr := {this};
      height := 1;
    }

    ghost predicate ValidInput(history: seq<(nat, Producer<nat>)>, next: nat)
      requires ValidHistory(history)
      decreases height
    {
      true
    }
    twostate predicate ValidOutput(history: seq<(nat, Producer<nat>)>, nextInput: nat, new nextOutput: Producer<nat>)
      decreases height
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)]) && fresh(nextOutput)
    }
    ghost predicate ValidHistory(history: seq<(nat, Producer<nat>)>)
      decreases height
    {
      true
    }

    method Invoke(x: nat) returns (result: Producer<nat>)
      requires Requires(x)
      reads Repr
      modifies Modifies(x)
      decreases Decreases(x).Ordinal()
      ensures Ensures(x, result)
    {
      result := new SeqProducer([x / 2, x - (x / 2)]);
      UpdateHistory(x, result);
    }

    ghost function Action(): Action<nat, Validatable> {
      this
    }

    twostate lemma ProducedAllNew(input: nat, new output: Validatable)
      requires old(Action().Valid())
      requires Action().ValidOutput(old(Action().history), input, output)
      ensures output.Valid()
      ensures fresh(output.Repr)
    {}
  }

  @IsolateAssertions
  method ExamplePipeline() {
    var upstream := new SeqProducer([1, 2, 3, 4, 5]);
    var mapping := new SplitAction();
    var processTotalProof := new DefaultTotalActionProof(mapping);
    assert fresh(upstream.Repr);
    assert fresh(mapping.Repr);
    assert fresh(processTotalProof.Repr);

    var mapped := new MappedProducer(upstream, mapping, processTotalProof);
    var flattened := new FlattenedProducer(mapped, processTotalProof);
    
    var collector := new Collector();

    var collectorTotalProof := new DefaultTotalActionProof(collector);
    flattened.ForEachRemaining(collector, collectorTotalProof);
    
    expect collector.values == [0, 1, 1, 1, 1, 2, 2, 2, 2, 3];
  }
}