/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Std.Producers {

  import opened Actions
  import opened BoundedInts
  import opened Consumers
  import opened Wrappers
  import opened Math
  import opened Frames
  import opened Termination
  import opened Ordinal
  import Collections.Seq

  // Actions that consume nothing and produce a T.
  @AssumeCrossModuleTermination
  trait IProducer<T> extends Action<(), T> {

    // For better readability
    method Next() returns (r: T)
      requires Requires(())
      reads Reads(())
      modifies Modifies(())
      decreases Decreases(())
      ensures Ensures((), r)
    {
      assert Requires(());

      r := Invoke(());
    }
  }

  // A proof that a given action only produces
  // elements from a given set.
  trait ProducesSetProof<I> {
    ghost function Action(): Action<(), I>
    ghost function Set(): set<I>

    lemma ProducesSet(history: seq<((), I)>)
      requires Action().ValidHistory(history)
      ensures |history| <= |Set()|
      ensures |history| < |Set()| ==> Action().ValidInput(history, ())
      ensures Seq.HasNoDuplicates(OutputsOf(history))
      ensures Seq.ToSet(OutputsOf(history)) <= Set()
  }

  @AssumeCrossModuleTermination
  class FunctionalIProducer<S, T> extends IProducer<T>, TotalActionProof<(), T> {

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

    constructor(state: S, stepFn: S -> (S, T))
      ensures Valid()
    {
      this.state := state;
      this.stepFn := stepFn;
      this.Repr := {this};
      this.history := [];
    }

    ghost function Action(): Action<(), T> {
      this
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

    lemma AnyInputIsValid(history: seq<((), T)>, next: ())
      requires Action().ValidHistory(history)
      ensures Action().ValidInput(history, next)
    {}
  }

  /* Actions that consume nothing and produce an Option<T>,
   * where None indicates there are no more values to produce. */
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

    twostate predicate ValidChange()
      reads this, Repr
      ensures ValidChange() ==> (
        && old(Valid()) && Valid()
        && fresh(Repr - old(Repr))
        && old(history) <= history
        && old(Produced()) <= Produced()
      )
    {
      var result :=
        && fresh(Repr - old(Repr))
        && old(Valid())
        && Valid()
        && old(history) <= history;
      if result then
        ProducedPrefix();
        result
      else
        result
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

    twostate lemma ProducedPrefix()
      requires old(ValidHistory(history))
      requires ValidHistory(history)
      requires old(history) <= history
      ensures Seq.Partitioned(old(Outputs()), IsSome)
      ensures Seq.Partitioned(Outputs(), IsSome)
      ensures old(Produced()) <= Produced()
    {
      assert Outputs() == old(Outputs()) + NewOutputs();
      Seq.PartitionedDecomposition(old(Outputs()), NewOutputs(), IsSome);
      ProducedComposition(old(Outputs()), NewOutputs());
    }

    twostate function NewProduced(): seq<T>
      requires old(ValidHistory(history))
      requires ValidHistory(history)
      requires old(history) <= history
      reads this, Repr
    {
      ProducedPrefix();
      Produced()[|old(Produced())|..]
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
    ghost function DecreasesMetric(): TerminationMetric
      requires Valid()
      reads this, Repr
      decreases Repr, 3

    ghost function Decreasing(): ORDINAL
      requires Valid()
      reads this, Repr
    {
      DecreasesMetric().Ordinal()
    }

    twostate predicate DecreasedBy(new result: Option<T>)
      requires old(Valid())
      requires Valid()
      reads this, Repr
    {
      if result.Some? then
        old(DecreasesMetric()).DecreasesTo(DecreasesMetric())
      else
        old(DecreasesMetric()).NonIncreasesTo(DecreasesMetric())
    }

    ghost function Decreases(t: ()): ORDINAL
      requires Requires(t)
      reads Reads(t)
    {
      Decreasing()
    }

    method Invoke(i: ()) returns (r: Option<T>)
      requires Requires(i)
      reads Reads(i)
      modifies Modifies(i)
      decreases Decreases(i), 0
      ensures Ensures(i, r)
      ensures DecreasedBy(r)

    // For better readability
    method Next() returns (r: Option<T>)
      requires Requires(())
      reads Reads(())
      modifies Modifies(())
      decreases Decreases(())
      ensures Ensures((), r)
      ensures DecreasedBy(r)
    {
      assert Requires(());

      AnyInputIsValid(history, ());
      r := Invoke(());
    }

    method ForEachRemaining(consumer: IConsumer<T>, ghost totalActionProof: TotalActionProof<T, ()>)
      requires Valid()
      requires consumer.Valid()
      requires Repr !! consumer.Repr !! totalActionProof.Repr
      requires totalActionProof.Valid()
      requires totalActionProof.Action() == consumer
      reads this, Repr, consumer, consumer.Repr, totalActionProof, totalActionProof.Repr
      modifies Repr, consumer.Repr
      ensures ValidChange()
      ensures consumer.ValidChange()
      ensures Done()
      ensures NewProduced() == consumer.NewInputs()

    // @IsolateAssertions
    // method ForEachRemaining'(consumer: Consumer<T>, ghost totalActionProof: TotalActionProof<T, bool>)
    //   requires Valid()
    //   requires consumer.Valid()
    //   requires Repr !! consumer.Repr !! totalActionProof.Repr
    //   requires totalActionProof.Valid()
    //   requires totalActionProof.Action() == consumer
    //   modifies Repr, consumer.Repr
    //   ensures Valid()
    //   ensures consumer.Valid()
    //   ensures Done() || consumer.Done()
    //   ensures ValidChange()
    //   ensures consumer.ValidChange()
    //   ensures NewProduced() == consumer.NewInputs()
    // {
    //   while true
    //     invariant ValidAndDisjoint()
    //     invariant consumer.ValidAndDisjoint()
    //     invariant Repr !! consumer.Repr
    //     invariant totalActionProof.Valid()
    //     invariant old(Produced()) <= Produced()
    //     invariant old(consumer.Inputs()) <= consumer.Inputs()
    //     invariant Produced()[|old(Produced())|..] == consumer.Inputs()[|old(consumer.Inputs())|..]
    //     decreases Decreasing()
    //   {
    //     label before:
    //     var t := Next();
    //     assert Seq.Partitioned(Outputs(), IsSome);
    //     assert Outputs() == old@before(Outputs()) + [t];
    //     Seq.PartitionedDecomposition(old@before(Outputs()), [t], IsSome);
    //     ProducedComposition(old@before(Outputs()), [t]);
         
    //     if t == None {
    //       assert Seq.Last(Outputs()).None?;
    //       assert Done();
    //       assert ProducedOf([t]) == [];
    //       assert Produced() == old@before(Produced());
    //       assert consumer.Inputs()[|old(consumer.Inputs())|..] == Produced()[|old(Produced())|..];
    //       break;
    //     }

    //     totalActionProof.AnyInputIsValid(consumer.history, t.value);
    //     var done := consumer.Accept(t.value);
    //     if done {
    //       break;
    //     }

    //     assert Seq.Last(consumer.Inputs()) == t.value;
    //     assert consumer.Inputs()[|old(consumer.Inputs())|..] == Produced()[|old(Produced())|..];
    //   }
    // }

    // True if this has outputted None at least once.
    // But note that !Done() does not guarantee that
    // the next output will be a Some!
    ghost predicate Done()
      reads this
      decreases Repr, 2
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

    ghost method ProduceNone()
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

    ghost method ProduceSome(value: T)
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

  @ResourceLimit("0")
  @IsolateAssertions
  method DefaultForEachRemaining<T>(producer: Producer<T>, consumer: IConsumer<T>, ghost totalActionProof: TotalActionProof<T, ()>)
    requires producer.Valid()
    requires consumer.Valid()
    requires producer.Repr !! consumer.Repr !! totalActionProof.Repr
    requires totalActionProof.Valid()
    requires totalActionProof.Action() == consumer
    reads producer, producer.Repr, consumer, consumer.Repr, totalActionProof, totalActionProof.Repr
    modifies producer.Repr, consumer.Repr
    ensures producer.ValidChange()
    ensures consumer.ValidChange()
    ensures producer.Done()
    ensures producer.NewProduced() == consumer.NewInputs()
  {
    producer.ValidImpliesValidChange();
    consumer.ValidImpliesValidChange();

    while true
      invariant fresh(producer.Repr - old(producer.Repr))
      invariant fresh(consumer.Repr - old(consumer.Repr))
      invariant producer.Repr !! consumer.Repr
      invariant totalActionProof.Valid()
      invariant producer.ValidChange()
      invariant consumer.ValidChange()
      invariant producer.NewProduced() == consumer.NewInputs()
      decreases producer.Decreasing()
    {
      label before:
      var t := producer.Next();
      assert Seq.Partitioned(producer.Outputs(), IsSome);
      assert producer.Outputs() == old@before(producer.Outputs()) + [t];
      Seq.PartitionedDecomposition(old@before(producer.Outputs()), [t], IsSome);
      ProducedComposition(old@before(producer.Outputs()), [t]);
        
      if t == None {
        assert Seq.Last(producer.Outputs()).None?;
        assert producer.Done();
        break;
      }
      
      totalActionProof.AnyInputIsValid(consumer.history, t.value);
      consumer.Accept(t.value);

      assert Seq.Last(consumer.Inputs()) == t.value;
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
    ensures |values| <= n ==> ProducedOf(result) == values
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

  method CollectToSeq<T>(p: Producer<T>) returns (s: seq<T>)
    requires p.Valid()
    requires p.history == []
    reads p, p.Repr
    modifies p.Repr
    ensures p.Valid()
    ensures p.Done()
    ensures p.Produced() == s
  {
    var seqWriter := new SeqWriter<T>();
    var writerTotalProof := seqWriter.totalActionProof();
    p.ForEachRemaining(seqWriter, writerTotalProof);
    return seqWriter.values;
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
    
    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()
    {}
  
    ghost predicate ValidOutputs(outputs: seq<Option<T>>)
      requires Seq.Partitioned(outputs, IsSome)
      decreases Repr
    {
      Seq.All(outputs, IsNone)
    }

    ghost function DecreasesMetric(): TerminationMetric
      requires Valid()
      reads this, Repr
      decreases Repr, 3
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
      ensures DecreasedBy(value)
    {
      assert Requires(t);

      value := None;

      OutputsPartitionedAfterOutputtingNone();
      ProduceNone();
      assert Valid();
    }

    method ForEachRemaining(consumer: IConsumer<T>, ghost totalActionProof: TotalActionProof<T, ()>)
      requires Valid()
      requires consumer.Valid()
      requires Repr !! consumer.Repr !! totalActionProof.Repr
      requires totalActionProof.Valid()
      requires totalActionProof.Action() == consumer
      reads this, Repr, consumer, consumer.Repr, totalActionProof, totalActionProof.Repr
      modifies Repr, consumer.Repr
      ensures ValidChange()
      ensures consumer.ValidChange()
      ensures Done()
      ensures NewProduced() == consumer.NewInputs()
    {
      DefaultForEachRemaining(this, consumer, totalActionProof);
    }
  }

  /** 
   * The equivalent of SeqReader(Seq.Repeat(n, t)),
   * But avoids actually creating the sequence of values.
   */
  class RepeatProducer<T> extends Producer<T> {

    // Note: it isn't great forcing a big integer in compiled code here,
    // but on the other hand this kind of producer is mostly useful
    // as a placeholder for bulk operations,
    // so it should rarely actually be invoked directly
    // for any large values of n anyway.
    const n: nat
    const t: T
    var remaining: nat

    constructor(n: nat, t: T)
      reads {}
      ensures Valid()
      ensures history == []
      ensures fresh(Repr)
      ensures this.n == n
      ensures this.t == t
      ensures history == []
    {
      this.n := n;
      this.t := t;
      this.remaining := n;
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
      && (0 < remaining ==> Seq.All(Outputs(), IsSome))
    }

    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()
    {}

    ghost predicate ValidOutputs(outputs: seq<Option<T>>)
      requires Seq.Partitioned(outputs, IsSome)
      decreases Repr
    {
      true
    }

    ghost function DecreasesMetric(): TerminationMetric
      requires Valid()
      reads this, Repr
      decreases Repr, 3
    {
      TMNat(remaining)
    }

    @IsolateAssertions
    method Invoke(i: ()) returns (value: Option<T>)
      requires Requires(i)
      reads Reads(i)
      modifies Modifies(i)
      decreases Decreases(i), 0
      ensures Ensures(i, value)
      ensures DecreasedBy(value)
    {
      assert Requires(i);
      assert Valid();

      if remaining == 0 {
        value := None;

        OutputsPartitionedAfterOutputtingNone();
        ProduceNone();

        old(DecreasesMetric()).NatNonIncreasesToNat(DecreasesMetric());
      } else {
        value := Some(t);

        OutputsPartitionedAfterOutputtingSome(t);
        ProduceSome(value.value);
        remaining := remaining - 1;

        old(DecreasesMetric()).NatDecreasesToNat(DecreasesMetric());
      }

      assert Valid();
    }

    method ForEachRemaining(consumer: IConsumer<T>, ghost totalActionProof: TotalActionProof<T, ()>)
      requires Valid()
      requires consumer.Valid()
      requires Repr !! consumer.Repr !! totalActionProof.Repr
      requires totalActionProof.Valid()
      requires totalActionProof.Action() == consumer
      reads this, Repr, consumer, consumer.Repr, totalActionProof, totalActionProof.Repr
      modifies Repr, consumer.Repr
      ensures ValidChange()
      ensures consumer.ValidChange()
      ensures Done()
      ensures NewProduced() == consumer.NewInputs()
    {
      DefaultForEachRemaining(this, consumer, totalActionProof);
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
      ensures this.elements == elements
      ensures index == 0
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
      && (Done() ==> index == |elements|)
      && index <= |elements|
      && Produced() == elements[..index]
      && (index < |elements| ==> Seq.All(Outputs(), IsSome))
    }

    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()
    {}
   
    ghost predicate ValidOutputs(outputs: seq<Option<T>>)
      requires Seq.Partitioned(outputs, IsSome)
      decreases Repr
    {
      true
    }

    ghost function DecreasesMetric(): TerminationMetric
      requires Valid()
      reads this, Repr
      decreases Repr, 3
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
      ensures DecreasedBy(value)
    {
      assert Requires(t);
      assert Valid();
      reveal TerminationMetric.Ordinal();

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

      assert Valid();
    }

    method ForEachRemaining(consumer: IConsumer<T>, ghost totalActionProof: TotalActionProof<T, ()>)
      requires Valid()
      requires consumer.Valid()
      requires Repr !! consumer.Repr !! totalActionProof.Repr
      requires totalActionProof.Valid()
      requires totalActionProof.Action() == consumer
      reads this, Repr, consumer, consumer.Repr, totalActionProof, totalActionProof.Repr
      modifies Repr, consumer.Repr
      ensures ValidChange()
      ensures consumer.ValidChange()
      ensures Done()
      ensures NewProduced() == consumer.NewInputs()
    {
      DefaultForEachRemaining(this, consumer, totalActionProof);
    }
  }

  // A proof that a given producer produces the elements from a given set.
  trait ProducerOfSetProof<T> {
    ghost function Producer(): Producer<T>
    ghost function Set(): set<T>

    lemma ProducesSet(history: seq<((), Option<T>)>)
      requires Producer().ValidHistory(history)
      ensures 
        var produced := ProducedOf(OutputsOf(history));
        && Seq.HasNoDuplicates(produced)
        && Seq.ToSet(produced) <= Set()
        && (!Seq.All(OutputsOf(history), IsSome) ==> Seq.ToSet(produced) == Set())
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

    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()
    {}

    ghost predicate ValidOutputs(outputs: seq<Option<T>>)
      requires Seq.Partitioned(outputs, IsSome)
      decreases Repr
    {
      true
    }

    ghost function DecreasesMetric(): TerminationMetric
      requires Valid()
      reads this, Repr
      decreases Repr, 3
    {
      TMNat(max - produced)
    }

    @ResourceLimit("1e7")
    method Invoke(t: ()) returns (value: Option<T>)
      requires Requires(t)
      reads this, Repr
      modifies Modifies(t)
      decreases Decreases(t), 0
      ensures Ensures(t, value)
      ensures DecreasedBy(value)
    {
      assert Requires(t);
      assert Valid();
      reveal TerminationMetric.Ordinal();

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
      assert Valid();
    }

    method ForEachRemaining(consumer: IConsumer<T>, ghost totalActionProof: TotalActionProof<T, ()>)
      requires Valid()
      requires consumer.Valid()
      requires Repr !! consumer.Repr !! totalActionProof.Repr
      requires totalActionProof.Valid()
      requires totalActionProof.Action() == consumer
      reads this, Repr, consumer, consumer.Repr, totalActionProof, totalActionProof.Repr
      modifies Repr, consumer.Repr
      ensures ValidChange()
      ensures consumer.ValidChange()
      ensures Done()
      ensures NewProduced() == consumer.NewInputs()
    {
      DefaultForEachRemaining(this, consumer, totalActionProof);
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

    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()
    {}

    ghost predicate ValidOutputs(outputs: seq<Option<T>>)
      requires Seq.Partitioned(outputs, IsSome)
      decreases Repr
    {
      true
    }

    ghost function DecreasesMetric(): TerminationMetric
      requires Valid()
      reads this, Repr
      decreases Repr, 3
    {
      TMSucc(source.DecreasesMetric())
    }

    @ResourceLimit("1e7")
    method Invoke(t: ()) returns (result: Option<T>)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t), 0
      ensures Ensures(t, result)
      ensures DecreasedBy(result)
    {
      assert Requires(t);
      assert Valid();

      result := None;
      var notFirstLoop := false;
      while true
        invariant fresh(Repr - old(Repr))
        invariant Valid()
        invariant history == old(history)
        invariant notFirstLoop ==>
                    && 0 < |source.Outputs()| && result == Seq.Last(source.Outputs())
        invariant source.DecreasedBy(result)
        invariant old(source.history) <= source.history
        invariant old(DecreasesMetric()).NonIncreasesTo(DecreasesMetric())
        decreases source.Decreasing()
      {
        notFirstLoop := true;

        old(DecreasesMetric()).SuccDecreasesToOriginal();
        result := source.Next();
        Repr := {this} + source.Repr;

        if result.None? || filter(result.value) {
          break;
        }

        if result.Some? {
          source.DoneIsOneWay();
        }

        old(DecreasesMetric()).SuccDecreasesToSucc(DecreasesMetric());
      }

      if result.Some? {
        assert Seq.Last(source.Outputs()) == result;
        Seq.PartitionedLastTrueImpliesAll(source.Outputs(), IsSome);
        var sourceNewOutputs := source.Outputs()[|old(source.Outputs())|..];
        assert source.Outputs() == old(source.Outputs()) + sourceNewOutputs;

        OutputsPartitionedAfterOutputtingSome(result.value);
        ProduceSome(result.value);
        assert (Seq.All(source.Outputs(), IsSome) ==> Seq.All(Outputs(), IsSome));

        old(DecreasesMetric()).SuccDecreasesToSucc(DecreasesMetric());
      } else {
        OutputsPartitionedAfterOutputtingNone();
        ProduceNone();
        assert !IsSome(Seq.Last(source.Outputs()));
        assert !Seq.All(source.Outputs(), IsSome);
        assert (Seq.All(source.Outputs(), IsSome) ==> Seq.All(Outputs(), IsSome));

        old(DecreasesMetric()).SuccNonIncreasesToSucc(DecreasesMetric());
      }

      assert Valid();
    }

    method ForEachRemaining(consumer: IConsumer<T>, ghost totalActionProof: TotalActionProof<T, ()>)
      requires Valid()
      requires consumer.Valid()
      requires Repr !! consumer.Repr !! totalActionProof.Repr
      requires totalActionProof.Valid()
      requires totalActionProof.Action() == consumer
      reads this, Repr, consumer, consumer.Repr, totalActionProof, totalActionProof.Repr
      modifies Repr, consumer.Repr
      ensures ValidChange()
      ensures consumer.ValidChange()
      ensures Done()
      ensures NewProduced() == consumer.NewInputs()
    {
      DefaultForEachRemaining(this, consumer, totalActionProof);
    }
  }

  class ConcatenatedProducer<T> extends Producer<T> {

    const first: Producer<T>
    const second: Producer<T>

    ghost const base: TerminationMetric

    constructor (first: Producer<T>, second: Producer<T>)
      requires first.Valid()
      requires first.history == []
      requires second.Valid()
      requires second.history == []
      requires first.Repr !! second.Repr
      reads first, first.Repr, second, second.Repr
      ensures Valid()
      ensures history == []
      ensures fresh(Repr - first.Repr - second.Repr)
    {
      this.first := first;
      this.second := second;
      this.base := TMSucc(second.DecreasesMetric());

      Repr := {this} + first.Repr + second.Repr;
      history := [];

      new;
      this.base.SuccDecreasesToOriginal();
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
      && base.DecreasesTo(second.DecreasesMetric())
      && ValidHistory(history)
      && (Seq.All(first.Outputs(), IsSome) || Seq.All(second.Outputs(), IsSome) ==> Seq.All(Outputs(), IsSome))
    }

    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()
    {}

    ghost predicate ValidOutputs(outputs: seq<Option<T>>)
      requires Seq.Partitioned(outputs, IsSome)
      decreases Repr
    {
      true
    }

    ghost function DecreasesMetric(): TerminationMetric
      requires Valid()
      reads this, Repr
      decreases Repr, 3
    {
      TMTuple(base, first.DecreasesMetric(), second.DecreasesMetric())
    }

    @ResourceLimit("1e7")
    method Invoke(t: ()) returns (result: Option<T>)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t), 0
      ensures Ensures(t, result)
      ensures DecreasedBy(result)
    {
      assert Requires(t);
      assert Valid();

      DecreasesMetric().TupleDecreasesToFirst();
      assert (Decreases(t), 0 decreases to first.Decreases(t), 0);
      result := first.Next();
      Repr := {this} + first.Repr + second.Repr;

      if result.Some? {
        first.OutputtingSomeMeansAllSome(result.value);
      } else {
        first.OutputtingNoneMeansNotAllSome();
        assert !Seq.All(first.Outputs(), IsSome);

        old(DecreasesMetric()).TupleDecreasesToSecond();
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

        old(DecreasesMetric()).TupleDecreasesToTuple(DecreasesMetric());
      } else {
        assert !Seq.All(first.Outputs(), IsSome);
        assert !Seq.All(second.Outputs(), IsSome);
        OutputsPartitionedAfterOutputtingNone();
        ProduceNone();

        old(DecreasesMetric()).TupleNonIncreasesToTuple(DecreasesMetric());
      }

      assert (Seq.All(first.Outputs(), IsSome) || Seq.All(second.Outputs(), IsSome) ==> Seq.All(Outputs(), IsSome));

      assert Valid();
    }

    method ForEachRemaining(consumer: IConsumer<T>, ghost totalActionProof: TotalActionProof<T, ()>)
      requires Valid()
      requires consumer.Valid()
      requires Repr !! consumer.Repr !! totalActionProof.Repr
      requires totalActionProof.Valid()
      requires totalActionProof.Action() == consumer
      reads this, Repr, consumer, consumer.Repr, totalActionProof, totalActionProof.Repr
      modifies Repr, consumer.Repr
      ensures ValidChange()
      ensures consumer.ValidChange()
      ensures Done()
      ensures NewProduced() == consumer.NewInputs()
    {
      DefaultForEachRemaining(this, consumer, totalActionProof);
    }
  }

  class MappedProducer<I, O> extends Producer<O> {

    const original: Producer<I>
    const mapping: Action<I, O>

    ghost const mappingTotalProof: TotalActionProof<I, O>
    ghost const base: TerminationMetric

    constructor (original: Producer<I>, mapping: Action<I, O>, ghost mappingTotalProof: TotalActionProof<I, O>)
      requires original.Valid()
      requires original.history == []
      requires mapping.Valid()
      requires mapping.history == []
      requires mappingTotalProof.Valid()
      requires mappingTotalProof.Action() == mapping
      requires original.Repr !! mapping.Repr !! mappingTotalProof.Repr
      reads original, original.Repr, mapping, mapping.Repr, mappingTotalProof, mappingTotalProof.Repr
      ensures Valid()
      ensures history == []
      ensures fresh(Repr - original.Repr - mapping.Repr - mappingTotalProof.Repr)
    {
      this.original := original;
      this.mapping := mapping;
      this.mappingTotalProof := mappingTotalProof;
      this.base := TMSucc(original.DecreasesMetric());

      Repr := {this} + original.Repr + mapping.Repr + mappingTotalProof.Repr;
      history := [];

      new;
      this.base.SuccDecreasesToOriginal();
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
      && base.DecreasesTo(original.DecreasesMetric())
      && (!original.Done() <==> !Done())
    }

    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()
    {}

    ghost predicate ValidOutputs(outputs: seq<Option<O>>)
      requires Seq.Partitioned(outputs, IsSome)
      decreases Repr
    {
      true
    }

    ghost function DecreasesMetric(): TerminationMetric
      requires Valid()
      reads this, Repr
      decreases Repr, 3
    {
      TMTuple(base, TMNat(0), original.DecreasesMetric())
    }

    @ResourceLimit("1e7")
    method Invoke(t: ()) returns (result: Option<O>)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t), 0
      ensures Ensures(t, result)
      ensures DecreasedBy(result)
    {
      assert Requires(t);
      assert Valid();
      DecreasesMetric().TupleDecreasesToSecond();
      assert Decreasing() > original.Decreasing();
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
      assert Valid();
      assert original.DecreasedBy(next);
      if next.Some? {
        old(DecreasesMetric()).TupleDecreasesToTuple(DecreasesMetric());
      } else {
        old(DecreasesMetric()).TupleNonIncreasesToTuple(DecreasesMetric());
      }
    }

    method ForEachRemaining(consumer: IConsumer<O>, ghost totalActionProof: TotalActionProof<O, ()>)
      requires Valid()
      requires consumer.Valid()
      requires Repr !! consumer.Repr !! totalActionProof.Repr
      requires totalActionProof.Valid()
      requires totalActionProof.Action() == consumer
      reads this, Repr, consumer, consumer.Repr, totalActionProof, totalActionProof.Repr
      modifies Repr, consumer.Repr
      ensures ValidChange()
      ensures consumer.ValidChange()
      ensures Done()
      ensures NewProduced() == consumer.NewInputs()
    {
      DefaultForEachRemaining(this, consumer, totalActionProof);
    }
  }

  trait ProducerOfNewProducers<T> extends Producer<Producer<T>> {

    ghost function MaxProduced(): TerminationMetric

    method Invoke(i: ()) returns (r: Option<Producer<T>>)
      requires Requires(())
      reads Reads(())
      modifies Modifies(())
      decreases Decreases(()), 0
      ensures Ensures((), r)
      ensures DecreasedBy(r)
      ensures r.Some? ==> JustProduced(r.value)

    twostate predicate JustProduced(new produced: Producer<T>)
      reads this, produced, produced.Repr
    {
      && produced.Valid()
      && fresh(produced.Repr)
      && Repr !! produced.Repr
      && produced.history == []
      && MaxProduced().DecreasesTo(produced.DecreasesMetric())
    }
  }

  class FlattenedProducer<T> extends Producer<T> {

    const original: ProducerOfNewProducers<T>
    var currentInner: Option<Producer<T>>

    constructor (original: ProducerOfNewProducers<T>)
      requires original.Valid()
      ensures Valid()
      ensures fresh(Repr - original.Repr)
    {
      this.original := original;

      this.history := [];
      this.Repr := {this} + original.Repr;
      this.currentInner := None;
    }

    ghost function BaseMetric(): TerminationMetric
      requires Valid()
      reads this, Repr
      decreases Repr, 1
    {
      TMSucc(original.MaxProduced())
    }

    ghost function InnerDecreasesMetric(): TerminationMetric
      requires Valid()
      reads this, Repr
      decreases Repr, 2
      ensures BaseMetric().DecreasesTo(InnerDecreasesMetric())
    {
      reveal TerminationMetric.Ordinal();
      if currentInner.Some? then
        var result := TMSucc(currentInner.value.DecreasesMetric());
        BaseMetric().SuccDecreasesToSucc(result);
        result
      else
        TMNat(0)
    }

    twostate lemma InnerDecreasesMetricNonIncreases()
      requires old(Valid())
      requires old(currentInner.Some?)
      requires Valid()
      requires currentInner.Some?
      requires old(currentInner.value) == currentInner.value
      requires old(currentInner.value.DecreasesMetric()).NonIncreasesTo(currentInner.value.DecreasesMetric())
      ensures old(InnerDecreasesMetric()).NonIncreasesTo(InnerDecreasesMetric())
    {
      old(InnerDecreasesMetric()).SuccNonIncreasesToSucc(InnerDecreasesMetric());
    }

    twostate lemma InnerDecreasesMetricDecreases()
      requires old(Valid())
      requires old(currentInner.Some?)
      requires Valid()
      requires currentInner.Some?
      requires old(currentInner.value) == currentInner.value
      requires old(currentInner.value.DecreasesMetric()).DecreasesTo(currentInner.value.DecreasesMetric())
      ensures old(InnerDecreasesMetric()).DecreasesTo(InnerDecreasesMetric())
    {
      old(InnerDecreasesMetric()).SuccDecreasesToSucc(InnerDecreasesMetric());
    }

    twostate lemma InnerDecreasesMetricDecreases2()
      requires old(Valid())
      requires old(currentInner.Some?)
      requires Valid()
      requires currentInner.None?
      ensures old(InnerDecreasesMetric()).DecreasesTo(InnerDecreasesMetric())
    {
      reveal TerminationMetric.Ordinal();
    }

    ghost function DecreasesMetric(): TerminationMetric
      requires Valid()
      reads this, Repr
      decreases Repr, 3
    {
      TMTuple(BaseMetric(), original.DecreasesMetric(), InnerDecreasesMetric())
    }

    // Makes it much easier to prove DecreasesMetric()
    // behaves correctly before updating the history at the end of Invoke()
    twostate lemma DecreasesMetricDoesntReadHistory()
      requires old(Valid())
      requires Valid()
      requires old(BaseMetric()) == BaseMetric()
      requires old(original.DecreasesMetric()) == original.DecreasesMetric()
      requires old(InnerDecreasesMetric()) == InnerDecreasesMetric()
      ensures old(DecreasesMetric()) == DecreasesMetric()
    {}

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
      && ValidHistory(history)
      && (currentInner.Some? ==>
            && 0 < |original.Outputs()|
            && currentInner == Seq.Last(original.Outputs())
            && original.MaxProduced().DecreasesTo(currentInner.value.DecreasesMetric()))
      && (!original.Done() && currentInner.Some? && !currentInner.value.Done() ==> !Done())
      && (Done() ==> original.Done() && currentInner.None?)
    }

    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()
    {}

    ghost predicate ValidOutputs(outputs: seq<Option<T>>)
      requires Seq.Partitioned(outputs, IsSome)
      decreases Repr
    {
      true
    }

    @ResourceLimit("1e8")
    method Invoke(t: ()) returns (result: Option<T>)
      requires Requires(t)
      reads this, Repr
      modifies Modifies(t)
      decreases Decreases(t), 0
      ensures Ensures(t, result)
      ensures DecreasedBy(result)
    {
      assert Valid();

      result := None;
      while result.None?
        invariant fresh(Repr - old(Repr))
        invariant Valid()
        invariant history == old(history)
        invariant fresh(original.Repr - old(original.Repr))
        invariant currentInner.Some? ==> fresh(currentInner.value.Repr - old(Repr))
        invariant result.Some? ==> !original.Done() && currentInner.Some? && !currentInner.value.Done()
        invariant old(original.history) <= original.history
        invariant old(Done()) == Done()
        invariant DecreasedBy(result)
        decreases original.Decreasing(), currentInner.Some?,
                  if currentInner.Some? then currentInner.value.Decreasing() else 0
      {
        if currentInner.None? {
          label beforeOriginalNext:
          ghost var historyBefore := original.history;
          old(DecreasesMetric()).TupleDecreasesToFirst();
          // Need to use Invoke() here for the extra postcondition from ProducerOfNewProducers
          currentInner := original.Invoke(());

          assert fresh(original.Repr - old@beforeOriginalNext(Repr));
          if currentInner.Some? {
            Repr := {this} + original.Repr + currentInner.value.Repr;

            assert ValidComponent(currentInner.value);

            assert old@beforeOriginalNext(original.Valid());
            assert currentInner.value.history == [];

            assert currentInner == Seq.Last(original.Outputs());
            Seq.PartitionedLastTrueImpliesAll(original.Outputs(), IsSome<Producer<T>>);
            assert !original.Done() && currentInner.Some? && !currentInner.value.Done();
            original.DoneIsOneWay();

            old(DecreasesMetric()).TupleDecreasesToTuple(DecreasesMetric());
            assert old(Decreasing()) >= Decreasing();
          } else {
            Repr := {this} + original.Repr;

            assert currentInner == Seq.Last(original.Outputs());
            assert original.Done() && currentInner.None?;

            old@beforeOriginalNext(DecreasesMetric()).TupleNonIncreasesToTuple(DecreasesMetric()) by {
              assert old@beforeOriginalNext(InnerDecreasesMetric()) == InnerDecreasesMetric();
            }

            break;
          }
        } else {
          label beforeCurrentInnerNext:

          DecreasesMetric().TupleDecreasesToSecond();
          assert DecreasesMetric().second == TMSucc(currentInner.value.DecreasesMetric());
          DecreasesMetric().second.SuccDecreasesToOriginal();
          result := currentInner.value.Next();
          this.Repr := {this} + original.Repr + currentInner.value.Repr;

          assert old@beforeCurrentInnerNext(currentInner.value.DecreasesMetric()).NonIncreasesTo(currentInner.value.DecreasesMetric());
          InnerDecreasesMetricNonIncreases@beforeCurrentInnerNext();
          old@beforeCurrentInnerNext(DecreasesMetric()).TupleNonIncreasesToTuple(DecreasesMetric());

          label afterCurrentInnerNext:

          if result.None? {

            var oldCurrentInner := currentInner;
            currentInner := None;

            InnerDecreasesMetricDecreases2@afterCurrentInnerNext();
            old@afterCurrentInnerNext(DecreasesMetric()).TupleDecreasesToTuple(DecreasesMetric());
            assert old(Decreasing()) >= Decreasing();
          } else {
            assert currentInner == Seq.Last(original.Outputs());
            assert original.ValidHistory(original.history);
            assert Seq.Partitioned(original.Outputs(), IsSome<Producer<T>>);
            Seq.PartitionedLastTrueImpliesAll(original.Outputs(), IsSome<Producer<T>>);
            assert result == Seq.Last(currentInner.value.Outputs());
            Seq.PartitionedLastTrueImpliesAll(currentInner.value.Outputs(), IsSome<T>);
            assert !original.Done() && currentInner.Some? && !currentInner.value.Done();

            original.DoneIsOneWay();
            assert !old(original.Done());
            currentInner.value.DoneIsOneWay@beforeCurrentInnerNext();

            InnerDecreasesMetricDecreases@beforeCurrentInnerNext();
            old@beforeCurrentInnerNext(DecreasesMetric()).TupleDecreasesToTuple(DecreasesMetric());
            assert old(Decreasing()) > Decreasing();
          }
        }
      }

      label beforeUpdatingHistory:
      if result.Some? {
        OutputsPartitionedAfterOutputtingSome(result.value);
        ProduceSome(result.value);

        DecreasesMetricDoesntReadHistory@beforeUpdatingHistory();
      } else {
        OutputsPartitionedAfterOutputtingNone();
        ProduceNone();

        DecreasesMetricDoesntReadHistory@beforeUpdatingHistory();
      }
      assert Valid();
    }


    method ForEachRemaining(consumer: IConsumer<T>, ghost totalActionProof: TotalActionProof<T, ()>)
      requires Valid()
      requires consumer.Valid()
      requires Repr !! consumer.Repr !! totalActionProof.Repr
      requires totalActionProof.Valid()
      requires totalActionProof.Action() == consumer
      reads this, Repr, consumer, consumer.Repr, totalActionProof, totalActionProof.Repr
      modifies Repr, consumer.Repr
      ensures ValidChange()
      ensures consumer.ValidChange()
      ensures Done()
      ensures NewProduced() == consumer.NewInputs()
    {
      DefaultForEachRemaining(this, consumer, totalActionProof);
    }
  }
}
