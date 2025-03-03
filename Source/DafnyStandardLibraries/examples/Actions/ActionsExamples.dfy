module ActionsExamples {
  import opened Std.Actions
  import opened Std.Producers
  import opened Std.Consumers
  import opened Std.Wrappers

  // Demonstration that actions can consume/produce reference values as well,
  // despite the usual challenges of quantifying over such types.

  class Box {
    const i: nat

    constructor(i: nat)
      reads {}
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
      decreases height
    {
      true
    }
    ghost predicate ValidHistory(history: seq<((), Box)>)
      decreases height
    {
      Seq.Map((b: Box) => b.i, OutputsOf(history)) == SeqRange(|history|)
    }

    method Invoke(t: ()) returns (r: Box)
      requires Requires(t)
      reads Reads(t)
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

    method RepeatUntil(t: (), stop: Box -> bool, ghost eventuallyStopsProof: ProducesTerminatedProof<(), Box>)
      requires Valid()
      requires eventuallyStopsProof.Action() == this
      requires eventuallyStopsProof.FixedInput() == t
      requires eventuallyStopsProof.StopFn() == stop
      requires forall i <- Inputs() :: i == t
      reads Repr
      modifies Repr
      decreases Repr
      ensures Valid()
    {
      DefaultRepeatUntil(this, t, stop, eventuallyStopsProof);
    }
  }

  method {:rlimit 0} BoxEnumeratorExample() {
    var enum: BoxEnumerator := new BoxEnumerator();
    assert |enum.Outputs()| == 0;
    var a := enum.Invoke(());

    assert enum.Outputs() == [a];
    assert Seq.Map((b: Box) => b.i, enum.Outputs()) == SeqRange(1) == [0];
    // assert a.i == 0;

    // var b := enum.Invoke(());
    // var c := enum.Invoke(());
    // var d := enum.Invoke(());
    // var e := enum.Invoke(());
  }

  method SetIProducerExample() {
    var s: set<nat> := {1, 2, 3, 4, 5};
    var copy: set<nat> := {};
    var e: SetIProducer<nat> := new SetIProducer(s);

    label before:
    for enumerated := 0 to 5
      invariant e.Valid()
      invariant enumerated == |e.history|
      invariant fresh(e.Repr)
    {
      var x := e.Invoke(());
      copy := copy + {x};
    }

    // TODO: cool enough that we can statically invoke
    // the enumerator the right number of times!
    // But now prove that copy == s!
    // assert |copy| == 5;
    // assert copy == s;
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
  class ExamplePipeline<T> extends Pipeline<T, T> {
    constructor(upstream: DynProducer<T>)
      requires upstream.Valid()
      ensures Valid()
    {
      this.upstream := upstream;
      var buffer := new Collector<T>();

      Repr := {this} + upstream.Repr + buffer.Repr;
      history := [];
      this.buffer := buffer;
      this.height := upstream.height + buffer.height + 1;
    }

    method Process(u: Option<T>, a: Consumer<T>)
      requires a.Valid()
      reads a.Repr
      modifies a.Repr
      ensures a.ValidAndDisjoint()
    {
      assert a.Valid();

      if u.Some? {
        a.AnyInputIsValid(a.history, u.value);
        a.Accept(u.value);
      }
    }
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