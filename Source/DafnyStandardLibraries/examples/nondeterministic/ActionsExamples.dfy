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
      decreases producer.Remaining()
    {
      var next := producer.Next();
      if next.None? {
        break;
      }

      firstTen := firstTen + [next.value];
    }

    expect firstTen == [0, 1, 1, 2, 3, 5, 8, 13, 21, 34];
  }

  // This could also easily be a Producer<T> instead.
  @AssumeCrossModuleTermination
  class SetReader<T(==)> extends IProducer<T> {
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
    var e: SetReader<nat> := new SetReader(s);

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
}