module ActionsExamples {
  import opened Std.Actions
  import opened Std.Producers
  import opened Std.Consumers
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
      decreases height, 0
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
      height := 0;
      new;
      Repr := {this, iter} + NonNullElements(iter._reads) + NonNullElements(iter._modifies) + NonNullElements(iter._new);
    }

    function NonNullElements(s: set<object?>): set<object> {
      s - {null}
    }

    ghost predicate ValidHistory(history: seq<((), nat)>)
      decreases height
    {
      true
    }
    ghost predicate ValidInput(history: seq<((), nat)>, next: ())
      decreases height
    {
      true
    }
    twostate predicate ValidOutput(history: seq<((), nat)>, nextInput: (), new nextOutput: nat)
      decreases height
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)])
    }

    method Invoke(i: ()) returns (o: nat)
      requires Requires(i)
      modifies Modifies(i)
      decreases Decreases(i).Ordinal(), 0
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

  method {:test} FibonnaciExample() {
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

    print firstTen, "\n";
    expect firstTen == [0, 1, 1, 2, 3, 5, 8, 13, 21, 34];
  }

  @AssumeCrossModuleTermination
  class SetIProducer<T(==)> extends IProducer<T>, ProducesSetProof<T> {
    ghost const original: set<T>
    var remaining: set<T>

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases height, 0
    {
      && this in Repr
      && ValidHistory(history)
      && remaining == original - Enumerated(history)
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
      height := 1;

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

    ghost function Enumerated(history: seq<((), T)>): set<T> {
      Seq.ToSet(OutputsOf(history))
    }

    ghost predicate ValidInput(history: seq<((), T)>, next: ())
      decreases height
    {
      |history| < |original|
    }
    twostate predicate ValidOutput(history: seq<((), T)>, nextInput: (), new nextOutput: T)
      requires ValidHistory(history)
      decreases height
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)])
    }

    ghost predicate ValidHistory(history: seq<((), T)>)
      decreases height
    {
      && |history| <= |original|
      && Seq.HasNoDuplicates(OutputsOf(history))
      && Enumerated(history) <= original
    }

    lemma EnumeratedCardinality()
      requires Valid()
      ensures |Enumerated(history)| == |history|
    {
      reveal Seq.ToSet();
      Seq.LemmaCardinalityOfSetNoDuplicates(OutputsOf(history));
    }

    method Invoke(i: ()) returns (o: T)
      requires Requires(i)
      modifies Modifies(i)
      decreases Decreases(i).Ordinal(), 0
      ensures Ensures(i, o)
    {
      EnumeratedCardinality();
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

    expect copy == s;
  }
}