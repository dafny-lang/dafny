module ActionsExamples {
  import opened Std.Actions
  import opened Std.Producers
  import opened Std.Consumers
  import opened Std.Wrappers

  // Demonstrating the simplest idiom
  // for looping over the values produced by a Producer<T>
  method SimpleProducerLoop() {
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

  // method SetIProducerExample() {
  //   var s: set<nat> := {1, 2, 3, 4, 5};
  //   var copy: set<nat> := {};
  //   var e: SetIProducer<nat> := new SetIProducer(s);

  //   label before:
  //   for enumerated := 0 to 5
  //     invariant e.Valid()
  //     invariant enumerated == |e.history|
  //     invariant fresh(e.Repr)
  //   {
  //     var x := e.Invoke(());
  //     copy := copy + {x};
  //   }

  //   // TODO: cool enough that we can statically invoke
  //   // the enumerator the right number of times!
  //   // But now prove that copy == s!
  //   // assert |copy| == 5;
  //   // assert copy == s;
  // }

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

  function Splitter(o: Option<nat>): seq<nat> {
    match o {
      case Some(x) => [x / 2, x - (x / 2)]
      case None => []
    }
  }

  @IsolateAssertions
  method ExamplePipeline() {
    var upstream := new SeqProducer([1, 2, 3, 4, 5]);
    var process := new FunctionAction(Splitter);
    var processTotalProof := new DefaultTotalActionProof(process);
    assert fresh(upstream.Repr);
    assert fresh(process.Repr);
    assert fresh(processTotalProof.Repr);

    var pipeline := new Pipeline(upstream, process, processTotalProof);
    
    var collector := new Collector();

    var collectorTotalProof := new DefaultTotalActionProof(collector);
    pipeline.ForEachRemaining(collector, collectorTotalProof);
    
    expect collector.values == [0, 1, 1, 1, 1, 2, 2, 2, 2, 3];
  }

  // method ComposedActionExample() {
  //   var addOne: Action<nat, nat> := new FunctionAction(x => x + 1);
  //   var double: Action<nat, nat> := new FunctionAction(x => x * 2);

  //   ghost var firstConsumesAll := new TotalFunctionTotalActionProof(addOne);
  //   ghost var secondConsumesAll := new TotalFunctionTotalActionProof(double);
  //   var composeProof := new TotalActionCompositionProof(firstConsumesAll, secondConsumesAll);

  //   var composed := new ComposedAction(addOne, double, composeProof);
  // }
}