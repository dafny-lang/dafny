module ActionsExamples {
  import opened Std.Actions
  import opened Std.Consumers
  import opened Std.Producers
  import opened Std.Termination
  import opened Std.Wrappers


  // Adapting an iterator to a producer

  iterator FibonacciIterator() yields (current: nat)
    ensures false
  {
    current := 0;
    yield;

    current := 1;
    var prev: nat := 0;
    yield;

    while true {
      var next := prev + current;
      prev := current;
      current := next;
      yield;
    }
  }

  @AssumeCrossModuleTermination
  class FibonacciProducer extends IProducer<nat> {

    const iter: FibonacciIterator

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases Repr, 0
    {
      && this in Repr
      && iter in Repr
      && this !in iter._reads && iter._reads <= Repr
      && this !in iter._modifies && iter._modifies <= Repr
      && this !in iter._new && iter._new <= Repr
      && iter.Valid()
    }

    twostate predicate ValidChange()
      reads this, Repr
      ensures ValidChange() ==> old(Valid()) && Valid()
      ensures ValidChange() ==> fresh(Repr - old(Repr))
      ensures ValidChange() ==> old(history) <= history
    {
      && fresh(Repr - old(Repr))
      && old(Valid())
      && Valid()
      && old(history) <= history
    }

    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()
    {}

    constructor ()
      ensures Valid()
      ensures fresh(Repr)
    {
      this.iter := new FibonacciIterator();
      new;
      Repr := {this, iter} + NonNullElements(iter._reads) + NonNullElements(iter._modifies) + NonNullElements(iter._new);
    }

    function NonNullElements(s: set<object?>): set<object> {
      s - {null}
    }

    ghost predicate ValidHistory(history: seq<((), nat)>)
      decreases Repr
    {
      true
    }
    ghost predicate ValidInput(history: seq<((), nat)>, next: ())
      decreases Repr
    {
      true
    }

    ghost function Decreases(i: ()): ORDINAL
      reads Reads(i)
    {
      ReprTerminationMetric().Ordinal()
    }

    method Invoke(i: ()) returns (o: nat)
      requires Requires(i)
      modifies Modifies(i)
      decreases Decreases(i), 0
      ensures Ensures(i, o)
    {
      var more := iter.MoveNext();
      assert history == old(history);
      assert more;

      o := iter.current;

      UpdateHistory(i, o);
      Repr := {this, iter} + NonNullElements(iter._reads) + NonNullElements(iter._modifies) + NonNullElements(iter._new);
    }
  }

  method {:test} FibonacciExample() {
    var iproducer := new FibonacciProducer();
    var iproducerTotalProof := new DefaultTotalActionProof(iproducer);
    var producer: Producer<nat> := new LimitedProducer(iproducer, 10, iproducerTotalProof);
    var firstTen: seq<nat> := [];

    while true
      invariant producer.Valid()
      invariant fresh(producer.Repr)
      decreases producer.Decreasing()
    {
      var next := producer.Next();
      if next.None? {
        break;
      }

      firstTen := firstTen + [next.value];
    }

    expect firstTen == [0, 1, 1, 2, 3, 5, 8, 13, 21, 34];
  }

  // Reading the elements of a set via an IProducer

  @AssumeCrossModuleTermination
  class SetIReader<T(==)> extends IProducer<T> {
    ghost const original: set<T>
    var remaining: set<T>

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases Repr, 0
    {
      && this in Repr
      && ValidHistory(history)
      && remaining == original - OutputSet(history)
    }

    twostate predicate ValidChange()
      reads this, Repr
      ensures ValidChange() ==> old(Valid()) && Valid()
      ensures ValidChange() ==> fresh(Repr - old(Repr))
      ensures ValidChange() ==> old(history) <= history
    {
      && fresh(Repr - old(Repr))
      && old(Valid())
      && Valid()
      && old(history) <= history
    }

    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()
    {}

    constructor(s: set<T>)
      ensures Valid()
      ensures fresh(Repr)
      ensures history == []
      ensures s == original
    {
      original := s;
      remaining := s;

      history := [];
      Repr := {this};

      reveal Seq.HasNoDuplicates();
      reveal Seq.ToSet();
    }

    ghost function Action(): Action<(), T> {
      this
    }

    ghost function Set(): set<T> {
      original
    }

    lemma ProducesSet(history: seq<((), T)>)
      requires Action().ValidHistory(history)
      ensures |history| <= |Set()|
      ensures Seq.ToSet(OutputsOf(history)) <= Set()
    {}

    ghost function OutputSet(history: seq<((), T)>): set<T> {
      Seq.ToSet(OutputsOf(history))
    }

    ghost predicate ValidInput(history: seq<((), T)>, next: ())
      decreases Repr
    {
      |history| < |original|
    }

    ghost predicate ValidHistory(history: seq<((), T)>)
      decreases Repr
    {
      && |history| <= |original|
      && Seq.HasNoDuplicates(OutputsOf(history))
      && OutputSet(history) <= original
    }

    ghost function Decreases(i: ()): ORDINAL
      reads Reads(i)
    {
      ReprTerminationMetric().Ordinal()
    }

    lemma OutputSetCardinality()
      requires Valid()
      ensures |OutputSet(history)| == |history|
    {
      reveal Seq.ToSet();
      Seq.LemmaCardinalityOfSetNoDuplicates(OutputsOf(history));
    }

    method Invoke(i: ()) returns (o: T)
      requires Requires(i)
      modifies Modifies(i)
      decreases Decreases(i), 0
      ensures Ensures(i, o)
    {
      OutputSetCardinality();
      assert 0 < |remaining|;

      o :| o in remaining;
      remaining := remaining - {o};

      UpdateHistory(i, o);
      Repr := {this};

      assert OutputsOf(history) == OutputsOf(old(history)) + [o];
      reveal Seq.ToSet();
      assert o !in OutputsOf(old(history));
      reveal Seq.HasNoDuplicates();
      Seq.LemmaNoDuplicatesInConcat(OutputsOf(old(history)), [o]);
    }
  }

  method {:test} SetIProducerExample() {
    var s: set<nat> := {1, 2, 3, 4, 5};
    var copy: set<nat> := {};
    var e: SetIReader<nat> := new SetIReader(s);

    for i := 0 to |s|
      invariant e.Valid()
      invariant i == |e.history| == |copy|
      invariant fresh(e.Repr)
      invariant copy == Seq.ToSet(e.Outputs())
    {
      ghost var oldOutputs := e.Outputs();

      var x := e.Next();

      e.ProducesSet(e.history);

      assert e.Outputs() == oldOutputs + [x];
      Seq.LemmaNoDuplicatesDecomposition(oldOutputs, [x]);
      assert x !in oldOutputs;

      copy := copy + {x};
    }

    // Needed to prove copy <= s && |copy| == |s| ==> copy == s
    Set.LemmaSubsetSize(copy, s);
    assert copy == s;
  }

  // Reading the elements of a set via a Producer.
  // This version takes quadratic time to traverse the elements of a set,
  // but the Std.ActionExterns.MakeSetReader() implementation
  // is linear.
  // This version is also a valuable feasibility proof
  // of the same ProducerOfSetProof<T> proof trait, however.

  @AssumeCrossModuleTermination
  class SetReader<T(==)> extends Producer<T>, ProducerOfSetProof<T> {
    ghost const original: set<T>
    var producedCount: nat
    var remaining: set<T>

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases Repr, 0
    {
      && this in Repr
      && ValidHistory(history)
      && producedCount == |Produced()|
      && remaining == original - OutputSet(history)
      && (0 < |remaining| ==> !Done())
    }

    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()
    {}

    constructor(s: set<T>)
      ensures Valid()
      ensures fresh(Repr)
      ensures history == []
      ensures s == original
    {
      original := s;
      remaining := s;
      producedCount := 0;

      history := [];
      Repr := {this};

      reveal Seq.HasNoDuplicates();
      reveal Seq.ToSet();
    }

    ghost function Producer(): Producer<T> {
      this
    }

    ghost function Set(): set<T> {
      original
    }

    lemma ProducesSet(history: seq<((), Option<T>)>)
      requires Producer().ValidHistory(history)
      ensures
        var produced := ProducedOf(OutputsOf(history));
        && Seq.HasNoDuplicates(produced)
        && Seq.ToSet(produced) <= Set()
        && (!Seq.All(OutputsOf(history), IsSome) ==> Seq.ToSet(produced) == Set())
    {}

    ghost function OutputSet(history: seq<((), Option<T>)>): set<T>
      requires Seq.Partitioned(OutputsOf(history), IsSome)
    {
      Seq.ToSet(ProducedOf(OutputsOf(history)))
    }

    ghost predicate ValidOutputs(outputs: seq<Option<T>>)
      requires Seq.Partitioned(outputs, IsSome)
      decreases Repr
    {
      var produced := ProducedOf(outputs);
      && Seq.HasNoDuplicates(produced)
      && Seq.ToSet(produced) <= Set()
      && (!Seq.All(outputs, IsSome) ==> Seq.ToSet(produced) == Set())
    }

    ghost function DecreasesMetric(): TerminationMetric
      requires Valid()
      reads this, Repr
      decreases Repr, 3
    {
      TMNat(|remaining|)
    }

    function ProducedCount(): nat
      reads this, Repr
      requires Valid()
      ensures ProducedCount() == |Produced()|
    {
      producedCount
    }

    function Remaining(): Option<nat>
      reads this, Repr
      requires Valid()
    {
      Some(|remaining|)
    }

    @ResourceLimit("1e8")
    method Invoke(i: ()) returns (r: Option<T>)
      requires Requires(i)
      modifies Modifies(i)
      decreases Decreases(i), 0
      ensures Ensures(i, r)
      ensures DecreasedBy(r)
    {
      assert Valid();
      if 0 < |remaining| {

        var o: T :| o in remaining;
        r := Some(o);
        remaining := remaining - {o};
        producedCount := producedCount + 1;

        reveal Seq.ToSet();
        reveal Seq.HasNoDuplicates();

        OutputsPartitionedAfterOutputtingSome(o);
        assert OutputsOf(history + [((), r)]) == OutputsOf(history) + [r];
        ProducedComposition(OutputsOf(history), [r]);
        ProduceSome(o);
      } else {
        r := None;

        OutputsPartitionedAfterOutputtingNone();
        assert OutputsOf(history + [((), r)]) == OutputsOf(history) + [r];
        ProducedComposition(OutputsOf(history), [r]);
        ProduceNone();
      }
      reveal TerminationMetric.Ordinal();

      assert Valid();
    }

    method ForEach(consumer: IConsumer<T>, ghost totalActionProof: TotalActionProof<T, ()>)
      requires Valid()
      requires consumer.Valid()
      requires Repr !! consumer.Repr !! totalActionProof.Repr
      requires totalActionProof.Valid()
      requires totalActionProof.Action() == consumer
      modifies Repr, consumer.Repr
      ensures ValidChange()
      ensures consumer.ValidChange()
      ensures Done()
      ensures NewProduced() == consumer.NewInputs()
    {
      DefaultForEach(this, consumer, totalActionProof);
    }

    method Fill(consumer: Consumer<T>, ghost totalActionProof: TotalActionProof<T, bool>)
      requires Valid()
      requires consumer.Valid()
      requires consumer.Capacity().Some?
      requires Repr !! consumer.Repr !! totalActionProof.Repr
      requires totalActionProof.Valid()
      requires totalActionProof.Action() == consumer
      modifies Repr, consumer.Repr
      ensures ValidChange()
      ensures consumer.ValidChange()
      ensures Done() || consumer.Capacity() == Some(0)
      ensures NewProduced() == consumer.NewConsumed()
    {
      DefaultFill(this, consumer, totalActionProof);
    }
  }

  @ResourceLimit("1e7")
  @IsolateAssertions
  method {:test} SetProducerExample() {
    var s: set<nat> := {1, 2, 3, 4, 5};
    var copy: set<nat> := {};
    var e: SetReader<nat> := new SetReader(s);

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

      if next.None? {
        assert Seq.Last(e.Outputs()) == None;
        assert e.Done();
        assert Seq.ToSet(e.Produced()) == s;
        break;
      }
      var x := next.value;

      e.ProducesSet(e.history);

      assert e.Produced() == oldProduced + [x];
      Seq.LemmaNoDuplicatesDecomposition(oldProduced, [x]);
      assert x !in oldProduced;

      copy := copy + {x};
    }

    assert copy == s;
    expect copy == s;
  }
}