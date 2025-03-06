

module Std.Producers {

  import opened Actions
  import opened Consumers
  import opened Wrappers
  import opened Math
  import Collections.Seq

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
  trait Producer<T> extends Action<(), Option<T>>, TotalActionProof<(), Option<T>> {

    ghost const limit: nat

    ghost function Action(): Action<(), Option<T>> {
      this
    }

    ghost predicate ValidInput(history: seq<((), Option<T>)>, next: ())
      requires ValidHistory(history)
      decreases height
    {
      true
    }

    ghost predicate ValidHistory(history: seq<((), Option<T>)>)
      decreases height
    {
      var outputs := OutputsOf(history);
      NoneTerminated(outputs) && ValidProduced(ProducedOf(outputs))
    }

    ghost function Produced(): seq<T> 
      requires ValidHistory(history)
      reads this, Repr
    {
      ProducedOf(OutputsOf(history))
    }

    ghost predicate ValidProduced(produced: seq<T>)
      decreases height

    lemma AnyInputIsValid(history: seq<((), Option<T>)>, next: ())
      requires Action().ValidHistory(history)
      ensures Action().ValidInput(history, next)
    {}

    lemma ProducesLessThanLimit(produced: seq<(T)>) 
      requires ValidProduced(produced)
      ensures |produced| <= limit

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
        InvokeDecreasesRemaining@before(r);
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
      // ensures Produced(e.Outputs()) == a.Inputs()
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

    // Note this is only a lower-bound on the actual
    // number of remaining elements,
    // and only used as a ghost measure
    // to prove termination of loops that consume elements.
    ghost function Remaining(): nat
      requires Valid()
      reads Repr
    {
      ProducesLessThanLimit(Produced());
      limit - |Produced()|
    }

    twostate lemma InvokeDecreasesRemaining(new nextProduced: Option<T>)
      requires old(Valid())
      requires Valid()
      requires Outputs() == old(Outputs()) + [nextProduced]
      ensures if nextProduced.Some? then
          Remaining() < old(Remaining())
        else
          Remaining() == old(Remaining())
    {
      var before := old(Action().Outputs());
      var after := Action().Outputs();
      assert NoneTerminated(before);
      assert NoneTerminated(after);
      ProducedComposition(before, [nextProduced]);
    }

    // Helper methods

    method ProduceNone()
      requires ValidHistory(history)
      requires ValidHistory(history + [((), None)])
      reads this, Repr
      modifies this`history
      ensures history == old(history) + [((), None)]
      ensures Produced() == old(Produced())
    {
      UpdateHistory((), None);

      NoneTerminatedCompositionRightAllNones(old(Outputs()), [None]);
      assert NoneTerminated(old(Outputs()));
      ProducedComposition(old(Outputs()), [None]);
      assert OutputsOf(history) == old(OutputsOf(history)) + [None];
      calc {
        Produced();
        ProducedOf(OutputsOf(history));
        ProducedOf(old(OutputsOf(history)) + [None]);
        ProducedOf(old(OutputsOf(history))) + ProducedOf(OutputsOf([((), None)]));
        old(Produced()) + ProducedOf([None]);
        old(Produced());
      }
    }

    method ProduceSome(value: T)
      requires ValidHistory(history)
      requires ValidHistory(history + [((), Some(value))])
      reads this, Repr
      modifies this`history
      ensures history == old(history) + [((), Some(value))]
      ensures Produced() == old(Produced()) + [value]
    {
      UpdateHistory((), Some(value));

      assert ValidHistory(old(history));
      assert NoneTerminated(old(Outputs()));
      NoneTerminatedLastIsSomeImpliesAllIsSome(Outputs());
      assert All(Outputs(), IsSome);
      assert Outputs() == old(Outputs()) + [Some(value)];
      AllDecomposition(old(Outputs()), [Some(value)], IsSome);
      assert All(old(Outputs()), IsSome);
      NoneTerminatedCompositionLeftAllNotNones(old(Outputs()), [Some(value)]);
      assert NoneTerminated(old(Outputs()));
      ProducedComposition(old(Outputs()), [Some(value)]);
      assert OutputsOf(history) == old(OutputsOf(history)) + [Some(value)];
      calc {
        Produced();
        ProducedOf(OutputsOf(history));
        ProducedOf(old(OutputsOf(history)) + [Some(value)]);
        ProducedOf(old(OutputsOf(history))) + ProducedOf(OutputsOf([((), Some(value))]));
        old(Produced()) + ProducedOf([Some(value)]);
        old(Produced()) + [value];
      }
    }
  }

  // TODO: Move some of these predicates as more general versions into Collections.Seq?

  predicate All<T>(s: seq<T>, p: T -> bool) {
    forall i {:trigger s[i]} | 0 <= i < |s| :: p(s[i])
  }

  lemma AllDecomposition<T>(left: seq<T>, right: seq<T>, p: T -> bool)
    requires All(left + right, p)
    ensures All(left, p)
    ensures All(right, p)
  {
    forall i: nat | i < |left| ensures p(left[i]) {
      assert (left + right)[i] == left[i];
    }
    forall i: nat | i < |right| ensures p(right[i]) {
      assert (left + right)[|left| + i] == right[i];
    }
  }

  predicate IsNone<T>(o: Option<T>) {
    o.None?
  }

  predicate IsSome<T>(o: Option<T>) {
    o.Some?
  }

  // TODO: Rework to be Partitioned?
  predicate NoneTerminated<T>(s: seq<Option<T>>) {
    if s == [] then
      true
    else if s[0].Some? then
      NoneTerminated(s[1..])
    else 
      All(s[1..], IsNone)
  }

  lemma NoneTerminatedFirstIsNoneImpliesAllIsNone<T>(s: seq<Option<T>>)
    requires NoneTerminated(s)
    requires 0 < |s|
    requires s[0].None?
    ensures All(s, IsNone)
  {}

  lemma NoneTerminatedLastIsSomeImpliesAllIsSome<T>(s: seq<Option<T>>)
    requires NoneTerminated(s)
    requires 0 < |s|
    requires Seq.Last(s).Some?
    ensures All(s, IsSome)
  {}

  function ProducedOf<T>(outputs: seq<Option<T>>): seq<T> 
    requires NoneTerminated(outputs)
  {
    if |outputs| == 0 || outputs[0].None? then
      []
    else
      [outputs[0].value] + ProducedOf(outputs[1..])
  }

  lemma ProducedOfAllNonesEmpty<T>(outputs: seq<Option<T>>)
    requires All(outputs, IsNone)
    ensures ProducedOf(outputs) == []
  {}

  lemma {:axiom} NoneTerminatedCompositionRightAllNones<T>(left: seq<Option<T>>, right: seq<Option<T>>)
    requires NoneTerminated(left)
    requires All(right, IsNone)
    ensures NoneTerminated(left + right)

  lemma {:axiom} NoneTerminatedCompositionLeftAllNotNones<T>(left: seq<Option<T>>, right: seq<Option<T>>)
    requires All(left, IsSome)
    requires NoneTerminated(right)
    ensures NoneTerminated(left + right)

  lemma NoneTerminatedDecomposition<T>(left: seq<Option<T>>, right: seq<Option<T>>)
    requires NoneTerminated(left + right)
    ensures NoneTerminated(left)
    ensures NoneTerminated(right)
  {
    if left == [] {
        assert right == left + right;
    } else {
      if left[0].None? {
        NoneTerminatedFirstIsNoneImpliesAllIsNone(left + right);
        AllDecomposition(left, right, IsNone);
        assert All(left, IsNone);
        NoneTerminatedDecomposition(left[1..], right);
      } else {
        var combined := left + right;
        assert combined[0].Some?;
        assert NoneTerminated(combined[1..]);
        assert combined[1..] == left[1..] + right;
        NoneTerminatedDecomposition(left[1..], right);
      }
    }
  }

  lemma ProducedComposition<T>(left: seq<Option<T>>, right: seq<Option<T>>)
    requires NoneTerminated(left)
    requires NoneTerminated(right)
    requires NoneTerminated(left + right)
    ensures ProducedOf(left + right) == ProducedOf(left) + ProducedOf(right)
  {
    var combined := left + right;
    if left == [] {
      assert left + right == right;
    } else {
      if left[0].None? {
        assert combined[0].None?;
        NoneTerminatedFirstIsNoneImpliesAllIsNone(combined);
        AllDecomposition(left, right, IsNone);
        assert ProducedOf(left) == ProducedOf(right) == [];
        ProducedOfAllNonesEmpty(left);
        assert ProducedOf(left + right) == ProducedOf(left) + ProducedOf(right);
      } else {
        assert ProducedOf(left) == [left[0].value] + ProducedOf(left[1..]); 
        assert NoneTerminated(left[1..]);
        assert left + right == [left[0]] + (left[1..] + right);
        assert NoneTerminated([left[0]] + (left[1..] + right));
        NoneTerminatedDecomposition([left[0]], left[1..] + right);
        assert NoneTerminated(left[1..] + right);
        assert ProducedOf(left + right) == [left[0].value] + ProducedOf(left[1..] + right); 
        assert NoneTerminated(left[1..] + right);
        
        ProducedComposition(left[1..], right);

        assert ProducedOf(left + right) == ProducedOf(left) + ProducedOf(right);
      }
    }
  }

  class LimitedProducer<T> extends Producer<T> {

    const original: IProducer<T>
    var produced: nat
    const max: nat

    ghost const originalTotalAction: TotalActionProof<(), T>

    constructor(original: IProducer<T>, max: nat, ghost originalTotalAction: TotalActionProof<(), T>)
      requires original.Valid()
      requires originalTotalAction.Valid()
      requires originalTotalAction.Action() == original
      requires original.Repr !! originalTotalAction.Repr
      ensures Valid()
      ensures history == []
      ensures fresh(Repr - original.Repr - originalTotalAction.Repr)
    {
      this.original := original;
      this.max := max;
      this.produced := 0;
      this.originalTotalAction := originalTotalAction;

      this.limit := max;
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
      && produced == |Produced()|
      && produced <= limit
    }

    twostate predicate ValidOutput(history: seq<((), Option<T>)>, nextInput: (), new nextOutput: Option<T>)
      decreases height
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)])
    }

    ghost predicate ValidProduced(produced: seq<T>)
      decreases height
    {
      |produced| <= limit
    }

    method Invoke(t: ()) returns (value: Option<T>)
      requires Requires(t)
      reads this, Repr
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
      ensures Ensures(t, value)
    {
      assert Requires(t);

      if produced == max {
        value := None;

        Repr := {this} + original.Repr + originalTotalAction.Repr;
        height := original.height + originalTotalAction.height + 1;
        ProduceNone();
      } else {
        originalTotalAction.AnyInputIsValid(original.history, ());
        var v := original.Invoke(());
        value := Some(v);
        produced := produced + 1;
        ProduceSome(v);
      }
    }

    lemma ProducesLessThanLimit(produced: seq<(T)>) 
      requires ValidProduced(produced)
      ensures |produced| <= limit
    {}
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

      limit := |elements|;
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
      && limit == |elements|
    }

    twostate predicate ValidOutput(history: seq<((), Option<T>)>, nextInput: (), new nextOutput: Option<T>)
      decreases height
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)])
    }
    ghost predicate ValidProduced(produced: seq<T>)
      decreases height
    {
      var index := |produced|;
      var values := Min(index, |elements|);
      var nones := index - values;
      produced == elements[..values]
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

    lemma ProducesLessThanLimit(produced: seq<(T)>) 
      requires ValidProduced(produced)
      ensures |produced| <= limit
    {
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

      limit := source.limit;
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
    ghost predicate ValidProduced(produced: seq<T>)
      decreases height
    {
      |produced| <= limit
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

    lemma ProducesLessThanLimit(produced: seq<(T)>) 
      requires ValidProduced(produced)
      ensures |produced| <= limit
    {}
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

      limit := first.limit + second.limit;
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
    ghost predicate ValidProduced(produced: seq<T>)
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

    lemma ProducesLessThanLimit(produced: seq<(T)>) 
      requires ValidProduced(produced)
      ensures |produced| <= limit
    {
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
    ghost predicate ValidProduced(produced: seq<T>)
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

    lemma ProducesLessThanLimit(produced: seq<(T)>) 
      requires ValidProduced(produced)
      ensures |produced| <= limit
    {
    }
  }
}
