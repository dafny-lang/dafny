
module Std.Producers {

  import opened Actions
  import opened Consumers
  import opened Wrappers
  import opened Math

  @AssumeCrossModuleTermination
  trait Producer<T> extends Action<(), T> {}

  // A proof that a given action only produces
  // elements from a given set.
  trait ProducesSetProof<I> {
    ghost function Action(): Action<(), I>
    ghost function Set(): set<I>

    lemma ProducesSet(history: seq<((), I)>)
      requires Action().ValidHistory(history)
      ensures |history| <= |Set()|
      ensures Seq.HasNoDuplicates(OutputsOf(history))
      ensures Seq.ToSet(OutputsOf(history)) <= Set()
  }

  class SetIProducer<T(==)> extends Producer<T>, ProducesSetProof<T> {
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
      reads Reads(i)
      modifies Modifies(i)
      decreases Decreases(i).Ordinal()
      ensures Ensures(i, o)
    {
      assert Requires(i);

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

    method RepeatUntil(i: (), stop: T -> bool, ghost eventuallyStopsProof: ProducesTerminatedProof<(), T>)
      requires Valid()
      requires eventuallyStopsProof.Action() == this
      requires eventuallyStopsProof.FixedInput() == i
      requires eventuallyStopsProof.StopFn() == stop
      requires forall i <- Inputs() :: i == i
      reads Repr
      modifies Repr
      decreases Repr
      ensures Valid()
    {
      DefaultRepeatUntil(this, i, stop, eventuallyStopsProof);
    }
  }

  // TODO: FunctionalDynProducer too?
  class FunctionalProducer<S, T> extends Producer<T> {

    const stepFn: S -> (S, T)
    var state: S

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases height, 0
    {
      this in Repr
    }

    constructor(state: S, stepFn: S -> (S, T)) {
      this.state := state;
      this.stepFn := stepFn;
    }

    ghost predicate ValidInput(history: seq<((), T)>, next: ())
      decreases height
    {
      true
    }
    ghost predicate ValidHistory(history: seq<((), T)>)
      decreases height
    {
      true
    }

    method Invoke(i: ()) returns (o: T)
      requires Requires(i)
      reads Repr
      modifies Modifies(i)
      decreases Decreases(i).Ordinal()
      ensures Ensures(i, o)
    {
      var (newState, result') := stepFn(state);
      state := newState;
      o := result';

      UpdateHistory(i, o);
    }

    method RepeatUntil(i: (), stop: T -> bool, ghost eventuallyStopsProof: ProducesTerminatedProof<(), T>)
      requires Valid()
      requires eventuallyStopsProof.Action() == this
      requires eventuallyStopsProof.FixedInput() == i
      requires eventuallyStopsProof.StopFn() == stop
      requires forall i <- Inputs() :: i == i
      reads Repr
      modifies Repr
      decreases Repr
      ensures Valid()
    {
      DefaultRepeatUntil(this, i, stop, eventuallyStopsProof);
    }
  }

  // Actions that consume nothing and produce an Option<T>, 
  // where None indicate there are no more values to produce.
  @AssumeCrossModuleTermination
  trait DynProducer<T> extends Action<(), Option<T>>, ProducesTerminatedProof<(), Option<T>> {
    ghost function Action(): Action<(), Option<T>> {
      this
    }
    ghost function FixedInput(): () {
      ()
    }
    ghost function StopFn(): Option<T> -> bool {
      StopWhenNone
    }
    ghost predicate StopWhenNone(r: Option<T>) {
      r.None?
    }

    ghost predicate ValidInput(history: seq<((), Option<T>)>, next: ())
      requires ValidHistory(history)
      decreases height
    {
      true
    }

    lemma AnyInputIsValid(history: seq<((), Option<T>)>, next: ())
      requires Action().ValidHistory(history)
      ensures Action().ValidInput(history, next)
    {}

    lemma ProducesTerminated(history: seq<((), Option<T>)>)
      requires Action().ValidHistory(history)
      requires forall i <- InputsOf(history) :: i == FixedInput()
      ensures exists n: nat | n <= Limit() :: Terminated(OutputsOf(history), StopFn(), n)

    // For better readability
    method Next() returns (r: Option<T>)
      requires Requires(())
      reads Reads(())
      modifies Modifies(())
      ensures Ensures((), r)
      ensures r.Some? ==> Remaining() < old(Remaining())
    {
      assert Requires(());

      AnyInputIsValid(history, ());
      label before:
      r := Invoke(());
      if r.Some? {
        assert forall i <- old(Action().Inputs()) :: i == ();
        InvokeUntilTerminationMetricDecreased@before(r);
      }
    }
  }

  function Enumerated<T>(produced: seq<Option<T>>): seq<T> {
    if |produced| == 0 || produced[0].None? then
      []
    else
      [produced[0].value] + Enumerated(produced[1..])
  }

  // TODO: This needs to be refactored to be just a helper method for
  //
  // Compose(e, a).RepeatUntil((), o -> o.None?)
  //
  // so that extern implementations of DynProducer that are push-based
  // can implement this by attaching `a` as a callback.
  //
  // TODO: It may make sense to have more than one ForEach as well: 
  // one that connects an IProducer and an IConsumer together and runs forever (decreases *),
  // one that connects an Producer and an Consumer with a proof that the consumer has adequate capacity,
  // and one that connects an Producer and an IConsumer with no additional proof obligation.
  method ForEach<T>(e: DynProducer<T>, a: Consumer<T>)
    requires e.Valid()
    requires a.Valid()
    requires e.Repr !! a.Repr
    modifies e.Repr, a.Repr
    // TODO: complete post-condition
    // ensures Enumerated(e.Outputs()) == a.Inputs()
  {
    var t := e.Next();
    while t != None
      invariant e.ValidAndDisjoint()
      invariant a.ValidAndDisjoint()
      invariant e.Repr !! a.Repr
      decreases e.Remaining()
    {
      a.AnyInputIsValid(a.history, t.value);
      a.Accept(t.value);

      t := e.Next();
      if t == None {
        break;
      }
    }
  }

  class SeqDynProducer<T> extends DynProducer<T> {

    const elements: seq<T>
    var index: nat

    constructor(elements: seq<T>)
      ensures Valid()
      ensures history == []
      ensures fresh(Repr)
    {
      this.elements := elements;
      this.index := 0;

      Repr := {this};
      history := [];
    }

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases height, 0
    {
      && this in Repr
      && ValidHistory(history)
    }

    ghost predicate ValidHistory(history: seq<((), Option<T>)>)
      decreases height
    {
      var index := |history|;
      var values := Min(index, |elements|);
      var nones := index - values;
      && (forall i <- InputsOf(history) :: i == ())
      && OutputsOf(history) == Seq.Map(x => Some(x), elements[..values]) + Seq.Repeat(None, nones)
    }

    method Invoke(t: ()) returns (value: Option<T>)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
      ensures Ensures(t, value)
    {
      assert Requires(t);

      if |elements| <= index {
        value := None;
      } else {
        value := Some(elements[index]);
        index := index + 1;
      }
      UpdateHistory((), value);
      // TODO: Doable but annoying
      assume {:axiom} ValidHistory(history);
      assert Valid();
    }


    method RepeatUntil(t: (), stop: Option<T> -> bool, ghost eventuallyStopsProof: ProducesTerminatedProof<(), Option<T>>)
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

    ghost function Limit(): nat {
      |elements|
    }

    lemma ProducesTerminated(history: seq<((), Option<T>)>)
      requires Action().ValidHistory(history)
      requires forall i <- InputsOf(history) :: i == FixedInput()
      ensures exists n: nat | n <= Limit() :: Terminated(OutputsOf(history), StopFn(), n)
    {
      assert Terminated(OutputsOf(history), StopFn(), |elements|);
    }

  }

  class FilteredDynProducer<T> extends DynProducer<T> {

    const source: DynProducer<T>
    const filter: T -> bool

    constructor (source: DynProducer<T>, filter: T -> bool)
      requires source.Valid()
      ensures Valid()
      ensures history == []
      ensures fresh(Repr - source.Repr)
    {
      this.source := source;
      this.filter := filter;

      Repr := {this} + source.Repr;
      height := source.height + 1;
      history := [];
    }

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases height, 0
    {
      && this in Repr
      && ValidComponent(source)
      && ValidHistory(history)
    }

    ghost predicate ValidHistory(history: seq<((), Option<T>)>)
      decreases height
    {
      true
    }

    @IsolateAssertions
    method Invoke(t: ()) returns (result: Option<T>)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
      ensures Ensures(t, result)
    {
      assert Requires(t);

      while true
        invariant fresh(Repr - old(Repr))
        invariant Valid()
        invariant ValidComponent(source)
        invariant history == old(history)
        decreases source.Remaining()
      {
        result := source.Next();
        Repr := {this} + source.Repr;

        if result.None? || filter(result.value) {
          break;
        }
      }

      UpdateHistory((), result);
    }

    method RepeatUntil(t: (), stop: Option<T> -> bool, ghost eventuallyStopsProof: ProducesTerminatedProof<(), Option<T>>)
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

    ghost function Limit(): nat {
      source.Limit()
    }

    lemma ProducesTerminated(history: seq<((), Option<T>)>)
      requires Action().ValidHistory(history)
      requires forall i <- InputsOf(history) :: i == FixedInput()
      ensures exists n: nat | n <= Limit() :: Terminated(OutputsOf(history), StopFn(), n)
    {
      // TODO
      assume {:axiom} Terminated(OutputsOf(history), StopFn(), Limit());
    }
  }


  trait Pipeline<U, T> extends DynProducer<T> {

    const upstream: DynProducer<U>
    const buffer: Collector<T>

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases height, 0
    {
      && this in Repr
      && ValidComponent(upstream)
      && ValidComponent(buffer)
      && upstream.Repr !! buffer.Repr
      && ValidHistory(history)
    }

    // TODO: needs refinement
    ghost predicate ValidHistory(history: seq<((), Option<T>)>)
      decreases height
    {
      true
    }

    method Invoke(t: ()) returns (r: Option<T>)
      requires Requires(t)
      reads Repr
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
      ensures Ensures(t, r)
    {
      label start:
      while |buffer.values| == 0
        invariant upstream.Repr !! buffer.Repr
        invariant fresh(Repr - old(Repr))
        invariant fresh(buffer.Repr - old(buffer.Repr))
        invariant fresh(upstream.Repr - old(upstream.Repr))
        invariant Valid()
        invariant buffer.ValidAndDisjoint()
        invariant upstream.ValidAndDisjoint()
        invariant history == old(history)
        modifies Repr
        decreases upstream.Remaining()
      {
        var u := upstream.Next();
        Repr := {this} + upstream.Repr + buffer.Repr;

        assume {:axiom} Repr !! buffer.Repr;
        Process(u, buffer);
        if u.None? {
          break;
        }
      }

      if 0 < |buffer.values| {
        var next := buffer.Pop();
        r := Some(next);
      } else {
        r := None;
      }
      UpdateHistory(t, r);

      assume {:axiom} Valid();
    }

    method Process(u: Option<U>, a: Consumer<T>)
      requires Valid()
      requires a.Valid()
      requires Repr !! a.Repr
      reads Repr, a.Repr
      modifies Repr, a.Repr
      ensures a.ValidAndDisjoint()
    // TODO: need a postcondition that a was invoked at least once etc

    method RepeatUntil(t: (), stop: Option<T> -> bool, ghost eventuallyStopsProof: ProducesTerminatedProof<(), Option<T>>)
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

    ghost function Limit(): nat {
      upstream.Limit()
    }

    lemma {:axiom} ProducesTerminated(history: seq<((), Option<T>)>)
      requires Action().ValidHistory(history)
      requires forall i <- InputsOf(history) :: i == FixedInput()
      ensures exists n: nat | n <= Limit() :: Terminated(OutputsOf(history), StopFn(), n)
    {
      // TODO
      assume {:axiom} false;
    }
  }
}
