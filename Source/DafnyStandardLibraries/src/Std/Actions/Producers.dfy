

module Std.Producers {

  import opened Actions
  import opened Consumers
  import opened Wrappers
  import opened Math

  @AssumeCrossModuleTermination
  trait IProducer<T> extends Action<(), T> {}

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

  class FunctionalIProducer<S, T> extends IProducer<T> {

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

    constructor(state: S, stepFn: S -> (S, T)) 
      ensures Valid()
    {
      this.state := state;
      this.stepFn := stepFn;
      this.Repr := {this};
      this.height := 0;
      this.history := [];
    }

    ghost predicate ValidHistory(history: seq<((), T)>)
      decreases height
    {
      true
    }
    ghost predicate ValidInput(history: seq<((), T)>, next: ())
      decreases height
    {
      true
    }
    twostate predicate ValidOutput(history: seq<((), T)>, nextInput: (), new nextOutput: T)
      decreases height
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)])
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
  }

  // Actions that consume nothing and produce an Option<T>, 
  // where None indicate there are no more values to produce.
  @AssumeCrossModuleTermination
  trait Producer<T> extends Action<(), Option<T>>, OutputsTerminatedProof<(), Option<T>> {
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

    lemma OutputsTerminated(history: seq<((), Option<T>)>)
      requires Action().ValidHistory(history)
      requires forall i <- InputsOf(history) :: i == FixedInput()
      ensures exists n: nat | n <= Limit() :: Terminated(OutputsOf(history), StopFn(), n)

    // For better readability
    method Next() returns (r: Option<T>)
      requires Requires(())
      reads Reads(())
      modifies Modifies(())
      ensures Ensures((), r)
      ensures if r.Some? then Remaining() < old(Remaining()) else Remaining() == old(Remaining())
    {
      assert Requires(());

      AnyInputIsValid(history, ());
      label before:
      r := Invoke(());
      if r.Some? {
        assert forall i <- old(Action().Inputs()) :: i == ();
        InvokeUntilTerminationMetricDecreased@before(r);
      } else {
        assume {:axiom} Remaining() == old(Remaining());
      }
    }

    @IsolateAssertions
    method ForEachRemaining(consumer: IConsumer<T>, ghost totalActionProof: TotalActionProof<T, ()>)
      requires Valid()
      requires consumer.Valid()
      requires Repr !! consumer.Repr !! totalActionProof.Repr
      requires totalActionProof.Valid()
      requires totalActionProof.Action() == consumer
      modifies Repr, consumer.Repr
      // TODO: complete post-condition
      // ensures Enumerated(e.Outputs()) == a.Inputs()
    {
      var t := Next();
      while t != None
        invariant ValidAndDisjoint()
        invariant consumer.ValidAndDisjoint()
        invariant Repr !! consumer.Repr
        invariant totalActionProof.Valid()
        decreases Remaining()
      {
        totalActionProof.AnyInputIsValid(consumer.history, t.value);
        consumer.Accept(t.value);

        t := Next();
        if t == None {
          break;
        }
      }
    }
  }

  class LimitedProducer<T> extends Producer<T> {

    const original: IProducer<T>
    const limit: nat
    var produced: nat

    ghost const originalTotalAction: TotalActionProof<(), T>

    constructor(original: IProducer<T>, limit: nat, ghost originalTotalAction: TotalActionProof<(), T>)
      requires original.Valid()
      requires originalTotalAction.Valid()
      requires originalTotalAction.Action() == original
      requires original.Repr !! originalTotalAction.Repr
      ensures Valid()
      ensures history == []
      ensures fresh(Repr - original.Repr - originalTotalAction.Repr)
    {
      this.original := original;
      this.limit := limit;
      this.produced := 0;
      this.originalTotalAction := originalTotalAction;

      Repr := {this} + original.Repr + originalTotalAction.Repr;
      history := [];
      height := original.height + originalTotalAction.height + 1;
    }

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases height, 0
    {
      && this in Repr
      && ValidComponent(original)
      && ValidComponent(originalTotalAction)
      && original.Repr !! originalTotalAction.Repr
      && originalTotalAction.Action() == original
      && ValidHistory(history)
      && produced <= limit
    }

    twostate predicate ValidOutput(history: seq<((), Option<T>)>, nextInput: (), new nextOutput: Option<T>)
      decreases height
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)])
    }
    ghost predicate ValidHistory(history: seq<((), Option<T>)>)
      decreases height
    {
      true
    }

    method Invoke(t: ()) returns (value: Option<T>)
      requires Requires(t)
      reads this, Repr
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
      ensures Ensures(t, value)
    {
      assert Requires(t);

      if produced == limit {
        value := None;
      } else {
        originalTotalAction.AnyInputIsValid(original.history, ());
        var v := original.Invoke(());
        value := Some(v);
        produced := produced + 1;
      }

      UpdateHistory(t, value);
      Repr := {this} + original.Repr + originalTotalAction.Repr;
      height := original.height + originalTotalAction.height + 1;
    }

    ghost function Limit(): nat {
      limit
    }

    lemma OutputsTerminated(history: seq<((), Option<T>)>)
      requires Action().ValidHistory(history)
      requires forall i <- InputsOf(history) :: i == FixedInput()
      ensures exists n: nat | n <= Limit() :: Terminated(OutputsOf(history), StopFn(), n)
    {
      assume {:axiom} Terminated(OutputsOf(history), StopFn(), limit);
    }
  }

  function Enumerated<T>(produced: seq<Option<T>>): seq<T> {
    if |produced| == 0 || produced[0].None? then
      []
    else
      [produced[0].value] + Enumerated(produced[1..])
  }

  class SeqProducer<T> extends Producer<T> {

    const elements: seq<T>
    var index: nat

    constructor(elements: seq<T>)
      ensures Valid()
      ensures history == []
      ensures fresh(Repr)
      reads {}
    {
      this.elements := elements;
      this.index := 0;

      Repr := {this};
      history := [];
      height := 0;
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

    twostate predicate ValidOutput(history: seq<((), Option<T>)>, nextInput: (), new nextOutput: Option<T>)
      decreases height
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)])
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
      assume {:axiom} ValidHistory(history);
      assert Valid();
    }

    ghost function Limit(): nat {
      |elements|
    }

    lemma OutputsTerminated(history: seq<((), Option<T>)>)
      requires Action().ValidHistory(history)
      requires forall i <- InputsOf(history) :: i == FixedInput()
      ensures exists n: nat | n <= Limit() :: Terminated(OutputsOf(history), StopFn(), n)
    {
      assert Terminated(OutputsOf(history), StopFn(), |elements|);
    }

  }

  class FilteredProducer<T> extends Producer<T> {

    const source: Producer<T>
    const filter: T -> bool

    constructor (source: Producer<T>, filter: T -> bool)
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
      && |history| <= |source.history|
    }

    twostate predicate ValidOutput(history: seq<((), Option<T>)>, nextInput: (), new nextOutput: Option<T>)
      decreases height
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)])
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
        height := source.height + 1;

        if result.None? || filter(result.value) {
          break;
        }
      }

      UpdateHistory((), result);
    }

    ghost function Limit(): nat {
      source.Limit()
    }

    lemma OutputsTerminated(history: seq<((), Option<T>)>)
      requires Action().ValidHistory(history)
      requires forall i <- InputsOf(history) :: i == FixedInput()
      ensures exists n: nat | n <= Limit() :: Terminated(OutputsOf(history), StopFn(), n)
    {
      var n :| Terminated(OutputsOf(history), StopFn(), n);
      assert n < source.Limit();
    }
  }

  class ConcatenatedProducer<T> extends Producer<T> {

    const first: Producer<T>
    const second: Producer<T>

    constructor (first: Producer<T>, second: Producer<T>)
      requires first.Valid()
      requires second.Valid()
      requires first.Repr !! second.Repr
      ensures Valid()
      ensures history == []
      ensures fresh(Repr - first.Repr - second.Repr)
    {
      this.first := first;
      this.second := second;

      Repr := {this} + first.Repr + second.Repr;
      height := first.height + second.height + 1;
      history := [];
    }

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases height, 0
    {
      && this in Repr
      && ValidComponent(first)
      && ValidComponent(second)
      && first.Repr !! second.Repr
      && ValidHistory(history)
    }

    twostate predicate ValidOutput(history: seq<((), Option<T>)>, nextInput: (), new nextOutput: Option<T>)
      decreases height
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)])
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

      result := first.Next();

      if result.None? {
        result := second.Next();
      }

      Repr := {this} + first.Repr + second.Repr;
      height := first.height + second.height + 1;
      UpdateHistory((), result);
    }

    ghost function Limit(): nat {
      first.Limit() + second.Limit()
    }

    lemma OutputsTerminated(history: seq<((), Option<T>)>)
      requires Action().ValidHistory(history)
      requires forall i <- InputsOf(history) :: i == FixedInput()
      ensures exists n: nat | n <= Limit() :: Terminated(OutputsOf(history), StopFn(), n)
    {
      assume {:axiom} Terminated(OutputsOf(history), StopFn(), Limit());
    }
  }

  // A producer that wraps another producer
  // and applies a transformation to each incoming element
  // that results in zero or more outgoing elements.
  // Essentially the Action equivalent of Seq.Flatten(Seq.Map(process, original)).
  //
  // Note that process accepts an Option<U> rather than a U,
  // so that it has awareness of when the original is exhausted
  // and can emit its own trailing elements if neccessary.
  //
  // It would arguably be better for process
  // to produce a Producer<T> instead of a seq<T>,
  // but that runs into limitations of the Action trait,
  // namely that it's not possible to ensure that
  // process only outputs Producers that are ValidAndDisjoint().
  //
  // Mainly provided so that external integrations
  // can recognize this pattern and optimize
  // for non-blocking push-based producers.
  class Pipeline<U, T> extends Producer<T> {

    const original: Producer<U>
    var originalDone: bool
    const process: Action<Option<U>, seq<T>>
    var currentInner: Producer?<T>

    ghost const processTotalProof: TotalActionProof<Option<U>, seq<T>>

    constructor (original: Producer<U>, process: Action<Option<U>, seq<T>>, ghost processTotalProof: TotalActionProof<Option<U>, seq<T>>)
      requires original.Valid()
      requires process.Valid()
      requires processTotalProof.Valid()
      requires processTotalProof.Action() == process
      requires original.Repr !! process.Repr !! processTotalProof.Repr
      ensures Valid()
      ensures fresh(Repr - original.Repr - process.Repr - processTotalProof.Repr)
    {
      this.original := original;
      this.originalDone := false;
      this.process := process;

      this.processTotalProof := processTotalProof;
      this.history := [];
      this.Repr := {this} + original.Repr + process.Repr + processTotalProof.Repr;
      this.height := original.height + process.height + processTotalProof.height + 1;
      this.currentInner := null;
    }

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases height, 0
    {
      && this in Repr
      && ValidComponent(original)
      && ValidComponent(process)
      && ValidComponent(processTotalProof)
      && (currentInner != null ==> ValidComponent(currentInner))
      && original.Repr !! process.Repr !! processTotalProof.Repr !!
          (if currentInner != null then currentInner.Repr else {})
      && ValidHistory(history)
      && processTotalProof.Action() == process
    }

    twostate predicate ValidOutput(history: seq<((), Option<T>)>, nextInput: (), new nextOutput: Option<T>)
      decreases height
      ensures ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)])
    }
    ghost predicate ValidHistory(history: seq<((), Option<T>)>)
      decreases height
    {
      true
    }

    @IsolateAssertions
    @ResourceLimit("0")
    method Invoke(t: ()) returns (r: Option<T>)
      requires Requires(t)
      reads this, Repr
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
      ensures Ensures(t, r)
    {
      r := None;

      while true
        invariant fresh(Repr - old(Repr))
        invariant Valid()
        invariant history == old(history)
        invariant processTotalProof.Valid()
        decreases original.Remaining(), !originalDone, currentInner,
                  if currentInner != null then currentInner.Remaining() else 0
      {
        label LoopEntry:
        assert true decreases to false;
        if currentInner == null {
          if originalDone {
            break;
          }

          var nextOuter := original.Next();
          Repr := {this} + original.Repr + process.Repr + processTotalProof.Repr;
          height := original.height + process.height + processTotalProof.height + 1;
          assert Valid();
          
          processTotalProof.AnyInputIsValid(process.history, nextOuter);

          var nextChunk := process.Invoke(nextOuter);
          Repr := {this} + original.Repr + process.Repr + processTotalProof.Repr;
          height := original.height + process.height + processTotalProof.height + 1;
          assert Valid();
          
          currentInner := new SeqProducer(nextChunk);
          assert currentInner.Valid();
          this.Repr := {this} + original.Repr + process.Repr + processTotalProof.Repr + currentInner.Repr;
          height := original.height + process.height + processTotalProof.height + currentInner.height + 1;
          assert ValidComponent(currentInner);

          originalDone := nextOuter.None?;
        } else {
          r := currentInner.Next();
          this.Repr := {this} + original.Repr + process.Repr + processTotalProof.Repr + currentInner.Repr;
          height := original.height + process.height + processTotalProof.height + currentInner.height + 1;
          assert Valid();

          if r.None? {
            currentInner := null;
          }
        }
      }

      UpdateHistory(t, r);
    }

    ghost function Limit(): nat {
      // TODO: Wrong, processing may produce more values.
      original.Limit()
    }

    lemma {:axiom} OutputsTerminated(history: seq<((), Option<T>)>)
      requires Action().ValidHistory(history)
      requires forall i <- InputsOf(history) :: i == FixedInput()
      ensures exists n: nat | n <= Limit() :: Terminated(OutputsOf(history), StopFn(), n)
    {
      assume {:axiom} false;
    }
  }
}
