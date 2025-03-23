

module Std.Producers {

  import opened Actions
  import opened Consumers
  import opened Wrappers
  import opened Math
  import opened Frames
  import opened Termination
  import opened Ordinal
  import Collections.Seq

  // Actions that consume nothing and produce a T.
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
      decreases Repr, 0
    {
      this in Repr
    }

    constructor(state: S, stepFn: S -> (S, T))
      ensures Valid()
    {
      this.state := state;
      this.stepFn := stepFn;
      this.Repr := {this};
      this.history := [];
    }

    ghost predicate ValidHistory(history: seq<((), T)>)
      decreases Repr
    {
      true
    }
    ghost predicate ValidInput(history: seq<((), T)>, next: ())
      decreases Repr
    {
      true
    }
    twostate predicate ValidOutput(history: seq<((), T)>, nextInput: (), new nextOutput: T)
      requires ValidHistory(history)
      decreases Repr
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)])
    }

    ghost function Decreases(t: ()): ORDINAL
      reads Reads(t)
    {
      0
    }

    method Invoke(i: ()) returns (o: T)
      requires Requires(i)
      reads Repr
      modifies Modifies(i)
      decreases Decreases(i), 0
      ensures Ensures(i, o)
    {
      var (newState, result') := stepFn(state);
      state := newState;
      o := result';

      UpdateHistory(i, o);
    }
  }

  // Actions that consume nothing and produce an Option<T>,
  // where None indicates there are no more values to produce.
  @AssumeCrossModuleTermination
  trait Producer<T> extends Action<(), Option<T>>, TotalActionProof<(), Option<T>> {

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases Repr, 0

    ghost function Action(): Action<(), Option<T>> {
      this
    }

    ghost predicate ValidInput(history: seq<((), Option<T>)>, next: ())
      requires ValidHistory(history)
      decreases Repr
    {
      true
    }

    ghost predicate ValidHistory(history: seq<((), Option<T>)>)
      decreases Repr
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
      decreases Repr

    lemma AnyInputIsValid(history: seq<((), Option<T>)>, next: ())
      requires Action().ValidHistory(history)
      ensures Action().ValidInput(history, next)
    {}

    // Termination metric ensuring Next() eventually returns None.
    // Not necessarily an exact measurement of the number of elements remaining,
    // only a conservative bound.
    ghost function RemainingMetric(): TerminationMetric
      requires Valid()
      reads this, Repr
      ensures RemainingMetric().Valid()

    ghost function Remaining(): ORDINAL
      requires Valid()
      reads this, Repr
    {
      RemainingMetric().Ordinal()
    }

    ghost function Decreases(t: ()): ORDINAL
      requires Requires(t)
      reads Reads(t)
    {
      Remaining()
    }

    method Invoke(i: ()) returns (r: Option<T>)
      requires Requires(i)
      reads Reads(i)
      modifies Modifies(i)
      decreases Decreases(i), 0
      ensures Ensures(i, r)
      ensures if r.Some? then
                old(Remaining()) > Remaining()
              else
                old(Remaining()) >= Remaining()

    method Next() returns (r: Option<T>)
      requires Requires(())
      reads Reads(())
      modifies Modifies(())
      decreases Decreases(())
      ensures Ensures((), r)
      ensures if r.Some? then
                old(Remaining()) > Remaining()
              else
                old(Remaining()) >= Remaining()
    {
      assert Requires(());

      AnyInputIsValid(history, ());
      r := Invoke(());
    }

    @IsolateAssertions
    method ForEachRemaining(consumer: IConsumer<T>, ghost totalActionProof: TotalActionProof<T, ()>)
      requires Valid()
      requires consumer.Valid()
      requires Repr !! consumer.Repr !! totalActionProof.Repr
      requires totalActionProof.Valid()
      requires totalActionProof.Action() == consumer
      modifies Repr, consumer.Repr
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

    // True if this has outputted None at least once.
    // But note that !Done() does not guarantee that
    // the next output will be a Some!
    ghost predicate Done()
      reads this
      decreases Repr, 1
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

    twostate lemma DoneIsOneWay()
      requires old(Valid())
      requires Valid()
      requires old(history) <= history
      ensures !Done() ==> old(!Done())
    {
      if !Done() {
        assert Seq.All(Outputs(), IsSome);
        assert old(Outputs()) <= Outputs();
      }
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

  /***********************
   * Simple Producers
   ***********************/

  class EmptyProducer<T> extends Producer<T> {

    constructor()
      ensures Valid()
      ensures history == []
      ensures fresh(Repr)
      reads {}
    {
      Repr := {this};
      history := [];
    }

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases Repr, 0
    {
      && this in Repr
      && ValidHistory(history)
    }

    twostate predicate ValidOutput(history: seq<((), Option<T>)>, nextInput: (), new nextOutput: Option<T>)
      decreases Repr
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)])
    }
    ghost predicate ValidOutputs(outputs: seq<Option<T>>)
      requires Seq.Partitioned(outputs, IsSome)
      decreases Repr
    {
      Seq.All(outputs, IsNone)
    }

    ghost function RemainingMetric(): TerminationMetric
      requires Valid()
      reads this, Repr
      ensures RemainingMetric().Valid()
    {
      TMNat(0)
    }

    @IsolateAssertions
    method Invoke(t: ()) returns (value: Option<T>)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t), 0
      ensures Ensures(t, value)
      ensures if value.Some? then
                old(Remaining()) > Remaining()
              else
                old(Remaining()) >= Remaining()
    {
      assert Requires(t);

      value := None;

      OutputsPartitionedAfterOutputtingNone();
      ProduceNone();
    }
  }

  class SeqReader<T> extends Producer<T> {

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
    }

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases Repr, 0
    {
      && this in Repr
      && ValidHistory(history)
      && index <= |elements|
      && (index < |elements| ==> Seq.All(Outputs(), IsSome))
    }

    twostate predicate ValidOutput(history: seq<((), Option<T>)>, nextInput: (), new nextOutput: Option<T>)
      decreases Repr
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)])
    }
    ghost predicate ValidOutputs(outputs: seq<Option<T>>)
      requires Seq.Partitioned(outputs, IsSome)
      decreases Repr
    {
      true
    }

    ghost function RemainingMetric(): TerminationMetric
      requires Valid()
      reads this, Repr
      ensures RemainingMetric().Valid()
    {
      TMNat(|elements| - index)
    }

    @IsolateAssertions
    method Invoke(t: ()) returns (value: Option<T>)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t), 0
      ensures Ensures(t, value)
      ensures if value.Some? then
                old(Remaining()) > Remaining()
              else
                old(Remaining()) == Remaining()
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
    }
  }

  /***********************
   * Producer Combinators
   ***********************/

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

      Repr := {this} + original.Repr + originalTotalAction.Repr;
      history := [];
    }

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases Repr, 0
    {
      && this in Repr
      && ValidComponent(original)
      && ValidComponent(originalTotalAction)
      && original.Repr !! originalTotalAction.Repr
      && originalTotalAction.Action() == original
      && ValidHistory(history)
      && produced == |Produced()|
      && produced <= max
      && (produced < max ==> Seq.All(Outputs(), IsSome))
    }

    twostate predicate ValidOutput(history: seq<((), Option<T>)>, nextInput: (), new nextOutput: Option<T>)
      decreases Repr
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)])
    }

    ghost predicate ValidOutputs(outputs: seq<Option<T>>)
      requires Seq.Partitioned(outputs, IsSome)
      decreases Repr
    {
      true
    }

    ghost function RemainingMetric(): TerminationMetric
      requires Valid()
      reads this, Repr
      ensures RemainingMetric().Valid()
    {
      TMNat(max - produced)
    }

    @IsolateAssertions
    @ResourceLimit("0")
    method Invoke(t: ()) returns (value: Option<T>)
      requires Requires(t)
      reads this, Repr
      modifies Modifies(t)
      decreases Decreases(t), 0
      ensures Ensures(t, value)
      ensures if value.Some? then
                old(Remaining()) > Remaining()
              else
                old(Remaining()) >= Remaining()
    {
      assert Requires(t);

      if produced == max {
        value := None;

        OutputsPartitionedAfterOutputtingNone();
        ProduceNone();
      } else {
        originalTotalAction.AnyInputIsValid(original.history, ());
        var v := original.Invoke(());
        value := Some(v);
        produced := produced + 1;

        OutputsPartitionedAfterOutputtingSome(v);
        ProduceSome(v);
      }

      Repr := {this} + original.Repr + originalTotalAction.Repr;
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
      history := [];
    }

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases Repr, 0
    {
      && this in Repr
      && ValidComponent(source)
      && ValidHistory(history)
      && (!source.Done() ==> !Done())
    }

    twostate predicate ValidOutput(history: seq<((), Option<T>)>, nextInput: (), new nextOutput: Option<T>)
      decreases Repr
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)])
    }
    ghost predicate ValidOutputs(outputs: seq<Option<T>>)
      requires Seq.Partitioned(outputs, IsSome)
      decreases Repr
    {
      true
    }

    ghost function RemainingMetric(): TerminationMetric
      requires Valid()
      reads this, Repr
      ensures RemainingMetric().Valid()
    {
      TMDatatype([source.RemainingMetric()])
    }

    @ResourceLimit("0")
    method Invoke(t: ()) returns (result: Option<T>)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t), 0
      ensures Ensures(t, result)
      ensures if result.Some? then
                old(Remaining()) > Remaining()
              else
                old(Remaining()) >= Remaining()
    {
      assert Requires(t);

      result := None;
      var notFirstLoop := false;
      while true
        invariant fresh(Repr - old(Repr))
        invariant Valid()
        invariant history == old(history)
        invariant notFirstLoop ==>
                    && 0 < |source.Outputs()| && result == Seq.Last(source.Outputs())
        invariant if result.Some? then
                    old(source.Remaining()) > source.Remaining()
                  else
                    old(source.Remaining()) >= source.Remaining()
        invariant old(source.history) <= source.history
        invariant old(Remaining()) >= Remaining()
        decreases source.Remaining()
      {
        notFirstLoop := true;

        result := source.Next();
        Repr := {this} + source.Repr;

        if result.None? || filter(result.value) {
          break;
        }

        if result.Some? {
          source.DoneIsOneWay();
        }

        // PlusIncreasingOnLeft(old(source.Remaining()), source.Remaining(), 1);
      }

      if result.Some? {
        assert Seq.Last(source.Outputs()) == result;
        Seq.PartitionedLastTrueImpliesAll(source.Outputs(), IsSome);
        var sourceNewOutputs := source.Outputs()[|old(source.Outputs())|..];
        assert source.Outputs() == old(source.Outputs()) + sourceNewOutputs;

        OutputsPartitionedAfterOutputtingSome(result.value);
        ProduceSome(result.value);
        assert (Seq.All(source.Outputs(), IsSome) ==> Seq.All(Outputs(), IsSome));

        // SuccStrictlyIncreasing(old(source.Remaining()), source.Remaining());
      } else {
        OutputsPartitionedAfterOutputtingNone();
        ProduceNone();
        assert !IsSome(Seq.Last(source.Outputs()));
        assert !Seq.All(source.Outputs(), IsSome);
        assert (Seq.All(source.Outputs(), IsSome) ==> Seq.All(Outputs(), IsSome));

        // PlusIncreasingOnLeft(old(source.Remaining()), source.Remaining(), 1);
      }
    }
  }

  class ConcatenatedProducer<T> extends Producer<T> {

    const first: Producer<T>
    const second: Producer<T>

    ghost const base: ORDINAL

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

      Repr := {this} + first.Repr + second.Repr;
      history := [];
    }

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases Repr, 0
    {
      && this in Repr
      && ValidComponent(first)
      && ValidComponent(second)
      && first.Repr !! second.Repr
      && base > second.RemainingMetric().Ordinal()
      && ValidHistory(history)
      && (Seq.All(first.Outputs(), IsSome) || Seq.All(second.Outputs(), IsSome) ==> Seq.All(Outputs(), IsSome))
    }

    twostate predicate ValidOutput(history: seq<((), Option<T>)>, nextInput: (), new nextOutput: Option<T>)
      decreases Repr
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)])
    }
    ghost predicate ValidOutputs(outputs: seq<Option<T>>)
      requires Seq.Partitioned(outputs, IsSome)
      decreases Repr
    {
      true
    }

    ghost function RemainingMetric(): TerminationMetric
      requires Valid()
      reads this, Repr
      ensures RemainingMetric().Valid()
    {
      TMTuple(base, first.RemainingMetric(), second.RemainingMetric())
    }

    // @IsolateAssertions
    @ResourceLimit("0")
    method {:only} Invoke(t: ()) returns (result: Option<T>)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t), 0
      ensures Ensures(t, result)
      ensures if result.Some? then
                old(Remaining()) > Remaining()
              else
                old(Remaining()) >= Remaining()
    {
      assert Requires(t);

      RemainingMetric().TupleDecreasesToFirst();
      result := first.Next();
      Repr := {this} + first.Repr + second.Repr;

      if result.Some? {
        first.OutputtingSomeMeansAllSome(result.value);
      } else {
        first.OutputtingNoneMeansNotAllSome();
        assert !Seq.All(first.Outputs(), IsSome);

        RemainingMetric().TupleDecreasesToSecond();
        result := second.Next();
        Repr := {this} + first.Repr + second.Repr;

        if result.Some? {
          second.OutputtingSomeMeansAllSome(result.value);
        } else {
          second.OutputtingNoneMeansNotAllSome();
          assert !Seq.All(second.Outputs(), IsSome);
        }
      }

      if result.Some? {
        assert Seq.All(first.Outputs(), IsSome) || Seq.All(second.Outputs(), IsSome);
        assert Seq.All(Outputs(), IsSome);
        OutputsPartitionedAfterOutputtingSome(result.value);
        ProduceSome(result.value);

        old(RemainingMetric()).TupleDecreasesToTuple(RemainingMetric());
      } else {
        assert !Seq.All(first.Outputs(), IsSome);
        assert !Seq.All(second.Outputs(), IsSome);
        OutputsPartitionedAfterOutputtingNone();
        ProduceNone();

        old(RemainingMetric()).TupleNonIncreasesToTuple(RemainingMetric());
      }

      assert (Seq.All(first.Outputs(), IsSome) || Seq.All(second.Outputs(), IsSome) ==> Seq.All(Outputs(), IsSome));

      assert Valid();
    }
  }

  class MappedProducer<I, O> extends Producer<O> {

    const original: Producer<I>
    const mapping: Action<I, O>

    ghost const mappingTotalProof: TotalActionProof<I, O>

    constructor (original: Producer<I>, mapping: Action<I, O>, ghost mappingTotalProof: TotalActionProof<I, O>)
      requires original.Valid()
      requires original.history == []
      requires mapping.Valid()
      requires mapping.history == []
      requires mappingTotalProof.Valid()
      requires mappingTotalProof.Action() == mapping
      requires original.Repr !! mapping.Repr !! mappingTotalProof.Repr
      ensures Valid()
      ensures history == []
      ensures fresh(Repr - original.Repr - mapping.Repr - mappingTotalProof.Repr)
    {
      this.original := original;
      this.mapping := mapping;
      this.mappingTotalProof := mappingTotalProof;

      Repr := {this} + original.Repr + mapping.Repr + mappingTotalProof.Repr;
      history := [];
    }

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases Repr, 0
    {
      && this in Repr
      && ValidComponent(original)
      && ValidComponent(mapping)
      && ValidComponent(mappingTotalProof)
      && mappingTotalProof.Action() == mapping
      && original.Repr !! mapping.Repr !! mappingTotalProof.Repr
      && ValidHistory(history)
      && (!original.Done() <==> !Done())
    }

    twostate predicate ValidOutput(history: seq<((), Option<O>)>, nextInput: (), new nextOutput: Option<O>)
      decreases Repr
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)])
    }
    ghost predicate ValidOutputs(outputs: seq<Option<O>>)
      requires Seq.Partitioned(outputs, IsSome)
      decreases Repr
    {
      true
    }

    ghost function RemainingMetric(): TerminationMetric
      requires Valid()
      reads this, Repr
      ensures RemainingMetric().Valid()
    {
      TMDatatype([original.RemainingMetric()])
    }

    @ResourceLimit("0")
    method Invoke(t: ()) returns (result: Option<O>)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t), 0
      ensures Ensures(t, result)
      ensures if result.Some? then
                old(Remaining()) > Remaining()
              else
                old(Remaining()) >= Remaining()
    {
      assert Requires(t);
      assert Valid();
      // old(remainingMetric).OrdinalDecreases(original.remainingMetric);
      var next := original.Next();

      if next.Some? {
        mappingTotalProof.AnyInputIsValid(mapping.history, next.value);
        var nextValue := mapping.Invoke(next.value);
        result := Some(nextValue);

        original.OutputtingSomeMeansAllSome(next.value);
        OutputsPartitionedAfterOutputtingSome(result.value);
        ProduceSome(result.value);
      } else {
        result := None;

        original.OutputtingNoneMeansNotAllSome();
        OutputsPartitionedAfterOutputtingNone();
        ProduceNone();

        assert !IsSome(Seq.Last(Outputs()));
      }

      Repr := {this} + original.Repr + mapping.Repr + mappingTotalProof.Repr;
    }
  }

  trait OutputsNewProducersProof<I, O> {

    ghost function Action(): Action<I, Producer<O>>

    twostate lemma ProducedAllNew(input: I, new output: Producer<O>)
      requires old(Action().Valid())
      requires Action().ValidOutput(old(Action().history), input, output)
      ensures output.Valid()
      ensures fresh(output.Repr)
      ensures output.history == []
  }

  trait ProducesNewProducersProof<T> {

    ghost function Producer(): Producer<Producer<T>>

    twostate lemma ProducedAllNew(new produced: Producer<T>)
      requires old(Producer().Valid())
      requires Producer().ValidOutput(old(Producer().history), (), Some(produced))
      ensures produced.Valid()
      ensures fresh(produced.Repr)
      ensures Producer().Repr !! produced.Repr
      ensures produced.history == []
  }

  class FlattenedProducer<T> extends Producer<T> {

    const original: Producer<Producer<T>>
    var currentInner: Option<Producer<T>>

    ghost const producesNewProducersProof: ProducesNewProducersProof<T>

    constructor (original: Producer<Producer<T>>, ghost producesNewProducersProof: ProducesNewProducersProof<T>)
      requires original.Valid()
      requires producesNewProducersProof.Producer() == original
      ensures Valid()
      ensures fresh(Repr - original.Repr)
    {
      this.original := original;

      this.producesNewProducersProof := producesNewProducersProof;
      this.history := [];
      this.Repr := {this} + original.Repr;
      this.currentInner := None;
    }

    ghost static function InnerRemainingMetric(currentInner: Option<Producer<T>>): TerminationMetric
      reads if currentInner.Some? then {currentInner.value} else {}
    {
      TMTuple(Omega(), TMBool(currentInner.Some?),
              TMOrdinal(if currentInner.Some? then currentInner.value.Remaining() else 0))
    }

    ghost function RemainingMetric(): TerminationMetric
      requires Valid()
      reads this, Repr
      ensures RemainingMetric().Valid()
    {
      TMTuple(Omega(), TMOrdinal(original.Remaining()), TMOrdinal(InnerRemainingMetric(currentInner).Ordinal()))
    }

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases Repr, 0
    {
      && this in Repr
      && ValidComponent(original)
      && (currentInner.Some? ==> ValidComponent(currentInner.value))
      && original.Repr !! (if currentInner.Some? then currentInner.value.Repr else {})
      && producesNewProducersProof.Producer() == original
      && ValidHistory(history)
      && (currentInner.Some? ==> 0 < |original.Outputs()| && currentInner == Seq.Last(original.Outputs()))
      && (!original.Done() && currentInner.Some? && !currentInner.value.Done() ==> !Done())
      && (Done() ==> original.Done() && currentInner.None?)
    }

    twostate predicate ValidOutput(history: seq<((), Option<T>)>, nextInput: (), new nextOutput: Option<T>)
      requires ValidHistory(history)
      decreases Repr
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)])
    }
    ghost predicate ValidOutputs(outputs: seq<Option<T>>)
      requires Seq.Partitioned(outputs, IsSome)
      decreases Repr
    {
      true
    }

    @ResourceLimit("0")
    method Invoke(t: ()) returns (result: Option<T>)
      requires Requires(t)
      reads this, Repr
      modifies Modifies(t)
      decreases Decreases(t), 0
      ensures Ensures(t, result)
      ensures if result.Some? then
                old(Remaining()) > Remaining()
              else
                old(Remaining()) >= Remaining()
    {
      result := None;

      while result.None?
        invariant fresh(Repr - old(Repr))
        invariant Valid()
        invariant history == old(history)
        invariant fresh(original.Repr - old(Repr))
        invariant currentInner.Some? ==> fresh(currentInner.value.Repr - old(Repr))
        invariant result.Some? ==> !original.Done() && currentInner.Some? && !currentInner.value.Done()
        invariant old(original.history) <= original.history
        invariant old(Done()) == Done()
        invariant if result.Some? then
                    old(Remaining()) > Remaining()
                  else
                    old(Remaining()) >= Remaining()
        decreases original.Remaining(), currentInner.Some?,
                  if currentInner.Some? then currentInner.value.Remaining() else 0
      {
        if currentInner.None? {
          label beforeOriginalNext:
          ghost var historyBefore := original.history;
          // old(remainingMetric).DecreasesToTransitive(remainingMetric, original.remainingMetric);
          // old(remainingMetric).OrdinalDecreases(original.remainingMetric);
          currentInner := original.Next();

          assert fresh(original.Repr - old@beforeOriginalNext(Repr));
          if currentInner.Some? {
            producesNewProducersProof.ProducedAllNew@beforeOriginalNext(currentInner.value);
            Repr := {this} + original.Repr + currentInner.value.Repr;
          } else {
            Repr := {this} + original.Repr;
          }
          // remainingMetric := RemainingMetric(original, currentInner);

          assert currentInner.Some? ==> fresh(currentInner.value.Repr - old(Repr));
          assert ValidComponent(original);
          if currentInner.Some? {
            assert ValidComponent(currentInner.value);

            // assert old@beforeOriginalNext(remainingMetric).DecreasesTo(remainingMetric);
            // assert old(remainingMetric).NonIncreasesTo(old@beforeOriginalNext(remainingMetric));
            // old(remainingMetric).DecreasesToTransitive(old@beforeOriginalNext(remainingMetric), remainingMetric);
            assert old(Remaining()) > Remaining();
          }
          assert original.Repr !! (if currentInner.Some? then currentInner.value.Repr else {});

          if currentInner.None? {
            // assert old@beforeOriginalNext(remainingMetric).NonIncreasesTo(remainingMetric);
            // assert old(remainingMetric).NonIncreasesTo(old@beforeOriginalNext(remainingMetric));
            // old(remainingMetric).NonIncreasesToTransitive(old@beforeOriginalNext(remainingMetric), remainingMetric);
            assert old(Remaining()) >= Remaining();

            assert currentInner == Seq.Last(original.Outputs());
            assert original.Done() && currentInner.None?;
            break;
          } else {
            assert old@beforeOriginalNext(original.Valid());
            assert currentInner.value.history == [];

            assert currentInner == Seq.Last(original.Outputs());
            Seq.PartitionedLastTrueImpliesAll(original.Outputs(), IsSome);
            assert !original.Done() && currentInner.Some? && !currentInner.value.Done();
            original.DoneIsOneWay();
          }
        } else {
          label beforeCurrentInnerNext:
          // ghost var remainingMetricBefore := remainingMetric;
          // assert remainingMetric.DecreasesTo(currentInner.value.remainingMetric);
          // old(remainingMetric).DecreasesToTransitive(remainingMetric, currentInner.value.remainingMetric);
          // old(remainingMetric).OrdinalDecreases(currentInner.value.remainingMetric);

          result := currentInner.value.Next();
          this.Repr := {this} + original.Repr + currentInner.value.Repr;
          // remainingMetric := RemainingMetric(original, currentInner);

          label afterCurrentInnerNext:
          // ghost var remainingMetricBefore2 := remainingMetric;

          if result.None? {
            var oldCurrentInner := currentInner;
            currentInner := None;
            // remainingMetric := RemainingMetric(original, currentInner);

            // assert remainingMetricBefore.NonIncreasesTo(remainingMetricBefore2);
            // assert old@afterCurrentInnerNext(original.remainingMetric) == original.remainingMetric;
            // assert remainingMetricBefore2.rest.DecreasesTo(remainingMetric.rest);
            // assert remainingMetricBefore2.DecreasesTo(remainingMetric);
            // assert old(remainingMetric).NonIncreasesTo(remainingMetricBefore);
            // assert InnerRemainingMetric(oldCurrentInner).DecreasesTo(InnerRemainingMetric(currentInner));
            // assert RemainingMetric(original, oldCurrentInner).DecreasesTo(RemainingMetric(original, currentInner));
            // assert remainingMetric == RemainingMetric(original, currentInner);
            // assert remainingMetricBefore2 == RemainingMetric(original, oldCurrentInner);
            // old(remainingMetric).NonIncreasesToTransitive(remainingMetricBefore, remainingMetricBefore2);
            // old(remainingMetric).NonIncreasesToTransitive(remainingMetricBefore2, remainingMetric);
          } else {
            // remainingMetric := RemainingMetric(original, currentInner);

            assert currentInner == Seq.Last(original.Outputs());
            Seq.PartitionedLastTrueImpliesAll(original.Outputs(), IsSome);
            assert result == Seq.Last(currentInner.value.Outputs());
            Seq.PartitionedLastTrueImpliesAll(currentInner.value.Outputs(), IsSome);
            assert !original.Done() && currentInner.Some? && !currentInner.value.Done();

            original.DoneIsOneWay();
            assert !old(original.Done());
            currentInner.value.DoneIsOneWay@beforeCurrentInnerNext();

            // reveal TerminationMetric.DecreasesTo();
            // assert old@beforeCurrentInnerNext(remainingMetric).DecreasesTo(remainingMetric);
            // assert old(remainingMetric).NonIncreasesTo(old@beforeCurrentInnerNext(remainingMetric));
            // old(remainingMetric).DecreasesToTransitive(old@beforeCurrentInnerNext(remainingMetric), remainingMetric);
          }
        }
      }

      if result.Some? {
        OutputsPartitionedAfterOutputtingSome(result.value);
        ProduceSome(result.value);
      } else {
        OutputsPartitionedAfterOutputtingNone();
        ProduceNone();
      }
    }
  }
}
