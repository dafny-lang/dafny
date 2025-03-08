

module Std.Producers {

  import opened Actions
  import opened Consumers
  import opened Wrappers
  import opened Math
  import opened Frames
  import opened Termination
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
      requires ValidHistory(history)
      decreases height
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)])
    }

    method Invoke(i: ()) returns (o: T)
      requires Requires(i)
      reads Repr
      modifies Modifies(i)
      decreases Decreases(i).Ordinal(), 0
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

    ghost var remaining: TerminationMetric

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases height, 0

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
      Seq.Partitioned(outputs, IsSome) && ValidOutputs(outputs)
    }

    ghost function Produced(): seq<T> 
      requires ValidHistory(history)
      reads this, Repr
    {
      ProducedOf(OutputsOf(history))
    }

    ghost predicate ValidOutputs(outputs: seq<Option<T>>)
      requires Seq.Partitioned(outputs, IsSome)
      decreases height

    lemma AnyInputIsValid(history: seq<((), Option<T>)>, next: ())
      requires Action().ValidHistory(history)
      ensures Action().ValidInput(history, next)
    {}

    method Invoke(i: ()) returns (r: Option<T>)
      requires Requires(i)
      reads Reads(i)
      modifies Modifies(i)
      decreases Decreases(i).Ordinal(), 0
      ensures Ensures(i, r)
      ensures if r.Some? then 
          old(remaining).DecreasesTo(remaining)
        else
          old(remaining) == remaining

    method Next() returns (r: Option<T>)
      requires Requires(())
      reads Reads(())
      modifies Modifies(())
      decreases Decreases(()).Ordinal()
      ensures Ensures((), r)
      ensures if r.Some? then 
          old(remaining).DecreasesTo(remaining) && old(remaining).Ordinal() > remaining.Ordinal()
        else
          old(remaining) == remaining
    {
      assert Requires(());

      AnyInputIsValid(history, ());
      r := Invoke(());
      if r.Some? {
        old(remaining).OrdinalDecreases(remaining);
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
        decreases remaining.Ordinal()
      {
        totalActionProof.AnyInputIsValid(consumer.history, t.value);
        consumer.Accept(t.value);

        t := Next();
        if t == None {
          break;
        }
      }
    }

    ghost predicate Done() 
      requires Valid()
      reads this, Repr
    {
      !Seq.All(Outputs(), IsSome)
    }

    // Helper methods

    lemma OutputsPartitionedAfterOutputtingNone()
      requires ValidHistory(history)
      ensures Seq.Partitioned(OutputsOf(history + [((), None)]), IsSome)
    {
      assert Seq.Partitioned(Outputs(), IsSome);
      assert Seq.AllNot<Option<T>>([None], IsSome);
      Seq.PartitionedCompositionRight(Outputs(), [None], IsSome);
      assert OutputsOf(history + [((), None)]) == Outputs() + [None];
    }

    lemma OutputsPartitionedAfterOutputtingSome(value: T)
      requires ValidHistory(history)
      requires Seq.All<Option<T>>(OutputsOf(history), IsSome)
      ensures Seq.Partitioned(OutputsOf(history + [((), Some(value))]), IsSome)
    {
      assert Seq.Partitioned(Outputs(), IsSome);
      assert Seq.All<Option<T>>([Some(value)], IsSome);
      Seq.PartitionedCompositionLeft(Outputs(), [Some(value)], IsSome);
      assert OutputsOf(history + [((), Some(value))]) == Outputs() + [Some(value)];
    }

    twostate lemma OutputtingSomeMeansAllSome(new value: T)
      requires history == old(history) + [((), Some(value))]
      requires ValidHistory(history)
      ensures Seq.All(old(Outputs()), IsSome)
      ensures Seq.All(Outputs(), IsSome)
    {
      var result := Seq.Last(Outputs());
      Seq.PartitionedLastTrueImpliesAll(Outputs(), IsSome);
      assert Seq.All(Outputs(), IsSome);
      assert Outputs() == old(Outputs()) + [Some(value)];
      Seq.AllDecomposition(old(Outputs()), [Some(value)], IsSome);
      assert Seq.All(Outputs(), IsSome) == old(Seq.All(Outputs(), IsSome));
      assert Seq.All(Outputs(), IsSome);
      assert old(Outputs()) <= Outputs();
      assert old(Seq.All(Outputs(), IsSome));
      assert Seq.All(Outputs(), IsSome);
    }


    twostate lemma OutputtingNoneMeansNotAllSome()
      requires history == old(history) + [((), None)]
      requires ValidHistory(history)
      ensures !Seq.All(Outputs(), IsSome)
    {
      assert !IsSome(Seq.Last(Outputs()));
    } 

    method ProduceNone()
      requires ValidHistory(history)
      requires ValidHistory(history + [((), None)])
      reads this, Repr
      modifies this`history
      ensures history == old(history) + [((), None)]
      ensures Produced() == old(Produced())
    {
      UpdateHistory((), None);

      Seq.PartitionedCompositionRight(old(Outputs()), [None], IsSome);
      assert Seq.Partitioned(old(Outputs()), IsSome);
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
      ensures Seq.All(Outputs(), IsSome)
    {
      UpdateHistory((), Some(value));

      assert ValidHistory(old(history));
      assert Seq.Partitioned(old(Outputs()), IsSome);
      Seq.PartitionedLastTrueImpliesAll(Outputs(), IsSome);
      assert Seq.All(Outputs(), IsSome);
      assert Outputs() == old(Outputs()) + [Some(value)];
      Seq.AllDecomposition(old(Outputs()), [Some(value)], IsSome);
      assert Seq.All(old(Outputs()), IsSome);
      Seq.PartitionedCompositionLeft(old(Outputs()), [Some(value)], IsSome);
      assert Seq.Partitioned(old(Outputs()), IsSome);
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

  
  predicate IsNone<T>(o: Option<T>) {
    o.None?
  }

  predicate IsSome<T>(o: Option<T>) {
    o.Some?
  }

  function ProducedOf<T>(outputs: seq<Option<T>>): seq<T> 
    requires Seq.Partitioned(outputs, IsSome)
  {
    if |outputs| == 0 || outputs[0].None? then
      []
    else
      [outputs[0].value] + ProducedOf(outputs[1..])
  }

  lemma ProducedOfMapSome<T>(values: seq<T>)
    ensures Seq.Partitioned(Seq.Map(x => Some(x), values), IsSome)
    ensures ProducedOf(Seq.Map(x => Some(x), values)) == values
  {
    reveal Seq.Map();
    var somes := Seq.Map(x => Some(x), values);
    assert Seq.All(somes, IsSome);
    Seq.AllImpliesPartitioned(somes, IsSome);
    var produced := ProducedOf(Seq.Map(x => Some(x), values));
    if values == [] {
    } else {
      assert produced[0] == values[0];
      ProducedOfMapSome(values[1..]);
    }
  }

  ghost function OutputsForProduced<T>(values: seq<T>, n: nat): (result: seq<Option<T>>)
    ensures Seq.Partitioned(result, IsSome)
    ensures ProducedOf(result) <= values
  {
    var index := Min(|values|, n);
    var produced := values[..index];
    var somes := Seq.Map(x => Some(x), produced);
    Seq.AllImpliesPartitioned(somes, IsSome);
    var nones := Seq.Repeat(None, n - index);
    Seq.AllNotImpliesPartitioned(nones, IsSome);
    Seq.PartitionedCompositionRight(somes, nones, IsSome);
    ProducedOfMapSome(produced);
    assert ProducedOf(somes) == produced;
    assert ProducedOf(nones) == [];
    ProducedComposition(somes, nones);
    somes + nones
  }

  lemma OutputsForProducedNextIsSome<T>(values: seq<T>, n: nat)
    requires n < |values|
    ensures OutputsForProduced(values, n + 1) == OutputsForProduced(values, n) + [Some(values[n])]
  {}

  lemma OutputsForProducedNextIsNone<T>(values: seq<T>, n: nat)
    requires |values| <= n
    ensures OutputsForProduced(values, n + 1) == OutputsForProduced(values, n) + [None]
  {}

  lemma ProducedOfAllNonesEmpty<T>(outputs: seq<Option<T>>)
    requires Seq.All(outputs, IsNone)
    ensures ProducedOf(outputs) == []
  {}
  
  @IsolateAssertions
  lemma ProducedComposition<T>(left: seq<Option<T>>, right: seq<Option<T>>)
    requires Seq.Partitioned(left, IsSome)
    requires Seq.Partitioned(right, IsSome)
    requires Seq.Partitioned(left + right, IsSome)
    ensures ProducedOf(left + right) == ProducedOf(left) + ProducedOf(right)
  {
    var combined := left + right;
    if left == [] {
      assert left + right == right;
    } else {
      if left[0].None? {
        assert combined[0].None?;
        Seq.PartitionedFirstFalseImpliesAllNot(combined, IsSome);
        Seq.AllDecomposition(left, right, IsNone);
        assert ProducedOf(left) == ProducedOf(right) == [];
        ProducedOfAllNonesEmpty(left);
        assert ProducedOf(left + right) == ProducedOf(left) + ProducedOf(right);
      } else {
        assert ProducedOf(left) == [left[0].value] + ProducedOf(left[1..]); 
        assert Seq.Partitioned(left[1..], IsSome);
        assert left + right == [left[0]] + (left[1..] + right);
        assert Seq.Partitioned([left[0]] + (left[1..] + right), IsSome);
        Seq.PartitionedDecomposition([left[0]], left[1..] + right, IsSome);
        assert Seq.Partitioned(left[1..] + right, IsSome);
        assert ProducedOf(left + right) == [left[0].value] + ProducedOf(left[1..] + right); 
        assert Seq.Partitioned(left[1..] + right, IsSome);
        
        ProducedComposition(left[1..], right);

        assert ProducedOf(left + right) == ProducedOf(left) + ProducedOf(right);
      }
    }
  }

  class LimitedProducer<T> extends Producer<T> {

    const original: IProducer<T>
    var produced: nat
    const max: nat

    ghost var producedNone: bool;
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

      this.remaining := TMNat(max);
      Repr := {this} + original.Repr + originalTotalAction.Repr;
      history := [];
      height := original.height + originalTotalAction.height + 1;
      producedNone := false;
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
      && produced <= max
      && remaining == TMNat(max - produced)
      && (produced < max ==> Seq.All(Outputs(), IsSome))
    }

    twostate predicate ValidOutput(history: seq<((), Option<T>)>, nextInput: (), new nextOutput: Option<T>)
      decreases height
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)])
    }

    ghost predicate ValidOutputs(outputs: seq<Option<T>>)
      requires Seq.Partitioned(outputs, IsSome)
      decreases height
    {
      true
    }

    @IsolateAssertions
    @ResourceLimit("0")
    method Invoke(t: ()) returns (value: Option<T>)
      requires Requires(t)
      reads this, Repr
      modifies Modifies(t)
      decreases Decreases(t).Ordinal(), 0
      ensures Ensures(t, value)
      ensures if value.Some? then 
          old(remaining).DecreasesTo(remaining)
        else
          old(remaining) == remaining
    {
      assert Requires(t);

      if produced == max {
        value := None;

        OutputsPartitionedAfterOutputtingNone();
        ProduceNone();
        producedNone := true;
      } else {
        originalTotalAction.AnyInputIsValid(original.history, ());
        var v := original.Invoke(());
        value := Some(v);
        produced := produced + 1;

        OutputsPartitionedAfterOutputtingSome(v);
        ProduceSome(v);
        remaining := TMNat(max - produced);
        reveal TerminationMetric.DecreasesTo();
      }

      Repr := {this} + original.Repr + originalTotalAction.Repr;
      height := original.height + originalTotalAction.height + 1;
    }
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

      remaining := TMNat(|elements|);
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
      && index <= |elements|
      && remaining == TMNat(|elements| - index)
      && (index < |elements| ==> Seq.All(Outputs(), IsSome))
    }

    twostate predicate ValidOutput(history: seq<((), Option<T>)>, nextInput: (), new nextOutput: Option<T>)
      decreases height
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)])
    }
    ghost predicate ValidOutputs(outputs: seq<Option<T>>)
      requires Seq.Partitioned(outputs, IsSome)
      decreases height
    {
      true
    }

    @IsolateAssertions
    method Invoke(t: ()) returns (value: Option<T>)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal(), 0
      ensures Ensures(t, value)
      ensures if value.Some? then 
          old(remaining).DecreasesTo(remaining)
        else
          old(remaining) == remaining
    {
      assert Requires(t);

      if |elements| == index {
        value := None;

        OutputsPartitionedAfterOutputtingNone();
        ProduceNone();
      } else {
        value := Some(elements[index]);
        
        OutputsPartitionedAfterOutputtingSome(elements[index]);
        ProduceSome(value.value);
        index := index + 1;
      }
      remaining := TMNat(|elements| - index);
      reveal TerminationMetric.DecreasesTo();
    }
  }

  class FilteredProducer<T> extends Producer<T> {

    const source: Producer<T>
    // TODO: Document how I really don't want to use a ~>,
    // but can't use Seq.Filter unless I do.
    const filter: T -> bool

    constructor (source: Producer<T>, filter: T -> bool)
      requires source.Valid()
      ensures Valid()
      ensures history == []
      ensures fresh(Repr - source.Repr)
    {
      this.source := source;
      this.filter := filter;

      remaining := source.remaining;
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
      && remaining.EqualOrDecreasesTo(source.remaining)
      && (Seq.All(source.Outputs(), IsSome) ==> Seq.All(Outputs(), IsSome))
    }

    twostate predicate ValidOutput(history: seq<((), Option<T>)>, nextInput: (), new nextOutput: Option<T>)
      decreases height
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)])
    }
    ghost predicate ValidOutputs(outputs: seq<Option<T>>)
      requires Seq.Partitioned(outputs, IsSome)
      decreases height
    {
      true
    }

    @IsolateAssertions
    @ResourceLimit("0")
    method Invoke(t: ()) returns (result: Option<T>)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal(), 0
      ensures Ensures(t, result)
      ensures if result.Some? then 
          old(remaining).DecreasesTo(remaining)
        else
          old(remaining) == remaining
    {
      assert Requires(t);

      result := None;
      var notFirstLoop := false;
      while true
        invariant fresh(Repr - old(Repr))
        invariant Valid()
        invariant ValidComponent(source)
        invariant history == old(history)
        invariant notFirstLoop ==> 
          && 0 < |source.Outputs()| && result == Seq.Last(source.Outputs())
        invariant if result.Some? then 
            old(source.remaining).DecreasesTo(source.remaining)
          else
            old(source.remaining).EqualOrDecreasesTo(source.remaining)
        invariant old(source.Outputs()) <= source.Outputs()
        decreases source.remaining.Ordinal()
      {
        notFirstLoop := true;

        label beforeNext:
        // Doesn't help because we need to decrease from old(height)
        // HeightMetricDecreases(source);
        result := source.Next();
        if result.Some? {
          assert old@beforeNext(source.remaining).DecreasesTo(source.remaining);
          old(source.remaining).DecreasesToTransitive(old@beforeNext(source.remaining), source.remaining);
          remaining.DecreasesToTransitive(old@beforeNext(source.remaining), source.remaining);
        }

        Repr := {this} + source.Repr;
        height := source.height + 1;
        
        if result.None? || filter(result.value) {
          break;
        }

        if result.Some? {
          assert result == Seq.Last(source.Outputs());
          Seq.PartitionedLastTrueImpliesAll(source.Outputs(), IsSome);
          assert Seq.All(source.Outputs(), IsSome);
          assert old(Seq.All(source.Outputs(), IsSome)) ==> old(Seq.All(Outputs(), IsSome));
          assert Seq.All(Outputs(), IsSome) == old(Seq.All(Outputs(), IsSome));
          assert Seq.All(source.Outputs(), IsSome);
          assert old(source.Outputs()) <= source.Outputs();
          assert old(Seq.All(source.Outputs(), IsSome));
          assert Seq.All(Outputs(), IsSome);
        }
      }
      assert notFirstLoop;

      if result.Some? {
        assert Seq.Partitioned(source.Outputs(), IsSome);
        assert Seq.Last(source.Outputs()) == result;
        Seq.PartitionedLastTrueImpliesAll(source.Outputs(), IsSome);
        assert Seq.All(source.Outputs(), IsSome);
        var sourceNewOutputs := source.Outputs()[|old(source.Outputs())|..];
        assert source.Outputs() == old(source.Outputs()) + sourceNewOutputs;
        assert Seq.All(old(source.Outputs()), IsSome);
        assert Seq.All(Outputs(), IsSome);
        OutputsPartitionedAfterOutputtingSome(result.value);
        ProduceSome(result.value);
        assert (Seq.All(source.Outputs(), IsSome) ==> Seq.All(Outputs(), IsSome));

        remaining := source.remaining;
        old(remaining).DecreasesToTransitive(old(source.remaining), source.remaining);
        assert old(remaining).DecreasesTo(remaining);
        assert (remaining == source.remaining || remaining.DecreasesTo(source.remaining));
      } else {
        OutputsPartitionedAfterOutputtingNone();
        ProduceNone();
        assert !IsSome(Seq.Last(source.Outputs()));
        assert !Seq.All(source.Outputs(), IsSome);
        assert (Seq.All(source.Outputs(), IsSome) ==> Seq.All(Outputs(), IsSome));

        remaining := old(remaining);
        remaining.EqualOrDecreasesToTransitive(old(source.remaining), source.remaining);
        assert (remaining == source.remaining || remaining.DecreasesTo(source.remaining));
      }
    }
  }

  class ConcatenatedProducer<T> extends Producer<T> {

    const first: Producer<T>
    const second: Producer<T>

    constructor (first: Producer<T>, second: Producer<T>)
      requires first.Valid()
      requires first.history == []
      requires second.Valid()
      requires second.history == []
      requires first.Repr !! second.Repr
      ensures Valid()
      ensures history == []
      ensures fresh(Repr - first.Repr - second.Repr)
    {
      this.first := first;
      this.second := second;

      remaining := TMComma(first.remaining, second.remaining);
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
      && remaining == TMComma(first.remaining, second.remaining)
      && (Seq.All(first.Outputs(), IsSome) || Seq.All(second.Outputs(), IsSome) ==> Seq.All(Outputs(), IsSome))
    }

    twostate predicate ValidOutput(history: seq<((), Option<T>)>, nextInput: (), new nextOutput: Option<T>)
      decreases height
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)])
    }
    ghost predicate ValidOutputs(outputs: seq<Option<T>>)
      requires Seq.Partitioned(outputs, IsSome)
      decreases height
    {
      true
    }

    @IsolateAssertions
    @ResourceLimit("0")
    method Invoke(t: ()) returns (result: Option<T>)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal(), 0
      ensures Ensures(t, result)
      ensures if result.Some? then 
          old(remaining).DecreasesTo(remaining)
        else
          old(remaining) == remaining
    {
      assert Requires(t);

      HeightMetricDecreases(first);
      result := first.Next();

      if result.Some? {
        first.OutputtingSomeMeansAllSome(result.value);
      } else {
        first.OutputtingNoneMeansNotAllSome();
        assert !Seq.All(first.Outputs(), IsSome);

        HeightMetricDecreases(second);
        result := second.Next();

        if result.Some? {
          second.OutputtingSomeMeansAllSome(result.value);
        } else {
          second.OutputtingNoneMeansNotAllSome();
          assert !Seq.All(second.Outputs(), IsSome);
        }
      }
      
      remaining := TMComma(first.remaining, second.remaining);
      reveal TerminationMetric.DecreasesTo();

      Repr := {this} + first.Repr + second.Repr;
      height := first.height + second.height + 1;

      if result.Some? {
        assert Seq.All(first.Outputs(), IsSome) || Seq.All(second.Outputs(), IsSome);
        assert Seq.All(Outputs(), IsSome);
        OutputsPartitionedAfterOutputtingSome(result.value);
        ProduceSome(result.value);
      } else {
        assert !Seq.All(first.Outputs(), IsSome);
        assert !Seq.All(second.Outputs(), IsSome);
        OutputsPartitionedAfterOutputtingNone();
        ProduceNone();
      }

      
      assert (Seq.All(first.Outputs(), IsSome) || Seq.All(second.Outputs(), IsSome) ==> Seq.All(Outputs(), IsSome));
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
  // class Pipeline<U, T> extends Producer<T> {

  //   const original: Producer<U>
  //   var originalDone: bool
  //   const process: Action<Option<U>, seq<T>>
  //   var currentInner: Producer?<T>

  //   ghost const processTotalProof: TotalActionProof<Option<U>, seq<T>>

  //   constructor (original: Producer<U>, process: Action<Option<U>, seq<T>>, ghost processTotalProof: TotalActionProof<Option<U>, seq<T>>)
  //     requires original.Valid()
  //     requires process.Valid()
  //     requires processTotalProof.Valid()
  //     requires processTotalProof.Action() == process
  //     requires original.Repr !! process.Repr !! processTotalProof.Repr
  //     ensures Valid()
  //     ensures fresh(Repr - original.Repr - process.Repr - processTotalProof.Repr)
  //   {
  //     this.original := original;
  //     this.originalDone := false;
  //     this.process := process;

  //     this.processTotalProof := processTotalProof;
  //     this.history := [];
  //     this.Repr := {this} + original.Repr + process.Repr + processTotalProof.Repr;
  //     this.height := original.height + process.height + processTotalProof.height + 1;
  //     this.currentInner := null;
  //     this.remaining := original.remaining;
  //   }

  //   ghost predicate Valid()
  //     reads this, Repr
  //     ensures Valid() ==> this in Repr
  //     ensures Valid() ==> ValidHistory(history)
  //     decreases height, 0
  //   {
  //     && this in Repr
  //     && ValidComponent(original)
  //     && ValidComponent(process)
  //     && ValidComponent(processTotalProof)
  //     && (currentInner != null ==> ValidComponent(currentInner))
  //     && original.Repr !! process.Repr !! processTotalProof.Repr !!
  //         (if currentInner != null then currentInner.Repr else {})
  //     && ValidHistory(history)
  //     && processTotalProof.Action() == process
  //   }

  //   twostate predicate ValidOutput(history: seq<((), Option<T>)>, nextInput: (), new nextOutput: Option<T>)
  //     requires ValidHistory(history)
  //     decreases height
  //     ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
  //   {
  //     ValidHistory(history + [(nextInput, nextOutput)])
  //   }
  //   ghost predicate ValidOutputs(outputs: seq<Option<T>>)
  //     requires Seq.Partitioned(outputs, IsSome)
  //     decreases height
  //   {
  //     true
  //   }

  //   @IsolateAssertions
  //   @ResourceLimit("0")
  //   method Invoke(t: ()) returns (r: Option<T>)
  //     requires Requires(t)
  //     reads this, Repr
  //     modifies Modifies(t)
  //     decreases Decreases(t).Ordinal()
  //     ensures Ensures(t, r)
  //     ensures value.Some? ==> old(remaining).DecreasesTo(remaining)
  //   {
  //     r := None;

  //     while true
  //       invariant fresh(Repr - old(Repr))
  //       invariant Valid()
  //       invariant history == old(history)
  //       invariant processTotalProof.Valid()
  //       decreases original.remaining.Ordinal(), !originalDone, currentInner,
  //                 if currentInner != null then currentInner.remaining.Ordinal() else 0
  //     {
  //       label LoopEntry:
  //       assert true decreases to false;
  //       if currentInner == null {
  //         if originalDone {
  //           break;
  //         }

  //         var nextOuter := original.Next();
  //         Repr := {this} + original.Repr + process.Repr + processTotalProof.Repr;
  //         height := original.height + process.height + processTotalProof.height + 1;
  //         assert Valid();
          
  //         processTotalProof.AnyInputIsValid(process.history, nextOuter);

  //         var nextChunk := process.Invoke(nextOuter);
  //         Repr := {this} + original.Repr + process.Repr + processTotalProof.Repr;
  //         height := original.height + process.height + processTotalProof.height + 1;
  //         assert Valid();
          
  //         currentInner := new SeqProducer(nextChunk);
  //         assert currentInner.Valid();
  //         this.Repr := {this} + original.Repr + process.Repr + processTotalProof.Repr + currentInner.Repr;
  //         height := original.height + process.height + processTotalProof.height + currentInner.height + 1;
  //         assert ValidComponent(currentInner);

  //         originalDone := nextOuter.None?;
  //       } else {
  //         label before:
  //         r := currentInner.Next();
  //         if r.Some? {
  //           assert old@before(currentInner.remaining.Ordinal()) > currentInner.remaining.Ordinal();
  //         }
  //         this.Repr := {this} + original.Repr + process.Repr + processTotalProof.Repr + currentInner.Repr;
  //         height := original.height + process.height + processTotalProof.height + currentInner.height + 1;
  //         assert Valid();

  //         if r.None? {
  //           currentInner := null;
  //         }
  //       }
  //     }

  //     UpdateHistory(t, r);
  //   }
  // }
}
