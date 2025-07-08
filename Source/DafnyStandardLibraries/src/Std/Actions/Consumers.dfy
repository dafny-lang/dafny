/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Std.Consumers {

  import opened Actions
  import opened Wrappers
  import opened DynamicArray
  import opened Termination
  import Collections.Seq

  // Actions that consume a T and outputs nothing.
  @AssumeCrossModuleTermination
  trait IConsumer<T> extends Action<T, ()> {

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

    // For better readability
    method Accept(t: T)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t)
      ensures Ensures(t, ())
    {
      assert Requires(t);

      var r := Invoke(t);
      assert r == ();
    }
  }

  datatype ConsumerState<T> = ConsumerState(consumer: Consumer<T>, capacity: Option<nat>, history: seq<(T, bool)>){
    ghost predicate Valid() {
      && Seq.Partitioned(history, WasConsumed)
      && (!Seq.All(history, WasConsumed) && capacity.Some? ==> capacity.value == 0)
    }
    ghost predicate ValidChange(newer: ConsumerState<T>)
    {
      && newer.consumer == consumer
      && Valid()
      && newer.Valid()
      && history <= newer.history
      && (var newHistory := newer.history[|history|..];
          assert newer.history == history + newHistory;
          Seq.PartitionedDecomposition(history, newHistory, WasConsumed);
          ConsumedComposition(history, newHistory);
          && var newConsumed := ConsumedOf(newHistory);
          && capacity.Some? ==>
            && |newConsumed| <= capacity.value
            && (!Seq.All(newer.history, WasConsumed) ==> |newConsumed| == capacity.value)
            && newer.capacity == Some(capacity.value - |newConsumed|))
    }

    @ResourceLimit("0")
    @IsolateAssertions
    lemma ValidChangeTransitive(newer: ConsumerState<T>, now: ConsumerState<T>)
      requires ValidChange(newer) && newer.ValidChange(now)
      ensures ValidChange(now)
      ensures NewConsumed(now) == NewConsumed(newer) + newer.NewConsumed(now)
    {
      var newerHistory := newer.history[|history|..];
      var nowHistory := now.history[|newer.history|..];
      var newHistory := now.history[|history|..];
      assert now.history == (history + newerHistory) + nowHistory;
      assert now.history == history + (newerHistory + nowHistory);
      assert newHistory == newerHistory + nowHistory;
      assert now.history == history + newHistory;
      Seq.PartitionedDecomposition(history, newHistory, WasConsumed);
      assert Seq.Partitioned(history + newerHistory + nowHistory, WasConsumed);
      Seq.PartitionedDecomposition(history + newerHistory, nowHistory, WasConsumed);
      Seq.PartitionedDecomposition(history, newerHistory, WasConsumed);
      Seq.PartitionedDecomposition(history, newerHistory + nowHistory, WasConsumed);
      assert Seq.Partitioned(newHistory, WasConsumed);
      var newerConsumed := ConsumedOf(newerHistory);
      var nowConsumed := ConsumedOf(nowHistory);
      var newConsumed := ConsumedOf(newHistory);
      ConsumedComposition(history, newHistory);
      ConsumedComposition(newerHistory, nowHistory);
      ConsumedComposition(history + newerHistory, nowHistory);
      assert newConsumed == newerConsumed + nowConsumed;
      Seq.PartitionedDecomposition(history, newHistory, WasConsumed);
      ConsumedComposition(history, newHistory);

      if capacity.Some? {
        assert |newConsumed| <= capacity.value;
        assert (!Seq.All(history, WasConsumed) ==> |newConsumed| == capacity.value);
        assert now.capacity == Some(capacity.value - |newConsumed|);
      }
    }

    ghost function NewConsumed(newer: ConsumerState<T>): seq<T>
      requires ValidChange(newer)
    {
      var newHistory := newer.history[|history|..];
      assert newer.history == history + newHistory;
      Seq.PartitionedDecomposition(history, newHistory, WasConsumed);
      ConsumedOf(newHistory)
    }
  }

  // Actions that attempt to consume a T and eventually reach capacity and fail.
  @AssumeCrossModuleTermination
  trait Consumer<T> extends Action<T, bool> {

    ghost function State(): ConsumerState<T>
      requires Valid()
      reads this, Repr
    {
      ConsumerState(this, Capacity(), history)
    }

    twostate predicate ValidChange()
      reads this, Repr
      ensures ValidChange() ==> old(Valid()) && Valid()
      ensures ValidChange() ==> fresh(Repr - old(Repr))
      ensures ValidChange() ==> old(history) <= history
    {
      && old(Valid()) && Valid()
      && fresh(Repr - old(Repr))
      && old(history) <= history
      && old(State()).ValidChange(State())
    }

    // Termination metric ensuring Accept() eventually returns false.
    // Not necessarily an exact measurement of the capacity remaining,
    // only a conservative bound.
    ghost function DecreasesMetric(): TerminationMetric
      requires Valid()
      reads this, Repr
      decreases Repr, 3

    ghost function Decreases(t: T): ORDINAL
      requires Requires(t)
      reads Reads(t)
    {
      Decreasing()
    }

    ghost function Decreasing(): ORDINAL
      requires Valid()
      reads this, Repr
    {
      DecreasesMetric().Ordinal()
    }

    twostate predicate DecreasedBy(new result: bool)
      requires old(Valid())
      requires Valid()
      reads this, Repr
    {
      if result then
        old(DecreasesMetric()).DecreasesTo(DecreasesMetric())
      else
        old(DecreasesMetric()).NonIncreasesTo(DecreasesMetric())
    }

    // True if this has outputted false at least once.
    // But note that !Done() does not guarantee that
    // the next output will be a true!
    ghost predicate Done()
      reads this
      decreases Repr, 2
    {
      !Seq.All(Outputs(), IsTrue)
    }

    ghost predicate ValidHistory(history: seq<(T, bool)>)
      decreases Repr
    {
      Seq.Partitioned(history, WasConsumed)
    }

    // The number of times the action can be invoked
    // before it outputs false.
    // Capacity() is None iff this is not known.
    function Capacity(): Option<nat>
      reads this, Repr
      requires Valid()

    ghost function Consumed(): seq<T>
      requires ValidHistory(history)
      reads this, Repr
    {
      ConsumedOf(history)
    }

    twostate function NewConsumed(): seq<T>
      requires ValidChange()
      reads this, Repr
    {
      old(State()).NewConsumed(State())
    }

    method Invoke(t: T) returns (r: bool)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t), 0
      ensures Ensures(t, r)
      ensures DecreasedBy(r)

    // For better readability
    method Accept(t: T) returns (o: bool)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t), 0
      ensures Ensures(t, o)
      ensures DecreasedBy(o)
    {
      assert Requires(t);

      o := Invoke(t);
    }
  }

  predicate IsTrue(b: bool) {
    b == true
  }

  predicate IsFalse(b: bool) {
    b == false
  }

  predicate WasConsumed<T>(pair: (T, bool)) {
    pair.1
  }

  predicate WasNotConsumed<T>(pair: (T, bool)) {
    !pair.1
  }

  ghost function ConsumedOf<T>(history: seq<(T, bool)>): seq<T>
    requires Seq.Partitioned(history, WasConsumed)
  {
    if history == [] then
      []
    else
      var (input, accepted) := history[0];
      if accepted then
        [input] + ConsumedOf(history[1..])
      else
        ConsumedOf(history[1..])
  }

  lemma ConsumedOfAllNotConsumedEmpty<T>(history: seq<(T, bool)>)
    requires Seq.AllNot(history, WasConsumed)
    ensures ConsumedOf(history) == []
  {}

  lemma ConsumedOfMaxCardinality<T>(history: seq<(T, bool)>)
    requires Seq.Partitioned(history, WasConsumed)
    ensures |ConsumedOf(history)| <= |history|
  {}

  lemma ConsumedOfAllAccepted<T>(history: seq<(T, bool)>)
    requires Seq.Partitioned(history, WasConsumed)
    requires |ConsumedOf(history)| == |history|
    ensures OutputsOf(history) == Seq.Repeat(true, |history|)
  {
    if history == [] {
    } else {
      var first := history[0];
      var rest := history[1..];
      ConsumedComposition([first], rest);
      Seq.PartitionedDecomposition([first], rest, WasConsumed);
      assert ConsumedOf(history) == ConsumedOf([first]) + ConsumedOf(rest);
      ConsumedOfMaxCardinality(rest);
      reveal Seq.Repeat();
    }
  }

  @IsolateAssertions
  lemma ConsumedComposition<T>(left: seq<(T, bool)>, right: seq<(T, bool)>)
    requires Seq.Partitioned(left, WasConsumed)
    requires Seq.Partitioned(right, WasConsumed)
    requires Seq.Partitioned(left + right, WasConsumed)
    ensures ConsumedOf(left + right) == ConsumedOf(left) + ConsumedOf(right)
  {
    var combined := left + right;
    if left == [] {
      assert left + right == right;
    } else {
      if !left[0].1 {
        assert !combined[0].1;
        Seq.PartitionedFirstFalseImpliesAllNot(combined, WasConsumed);
        Seq.AllNotDecomposition(left, right, WasConsumed);
        ConsumedOfAllNotConsumedEmpty(left);
        ConsumedOfAllNotConsumedEmpty(right);
        ConsumedOfAllNotConsumedEmpty(left + right);
        assert ConsumedOf(left) == ConsumedOf(right) == [];
        assert ConsumedOf(left + right) == ConsumedOf(left) + ConsumedOf(right);
      } else {
        assert ConsumedOf(left) == [left[0].0] + ConsumedOf(left[1..]);
        assert Seq.Partitioned(left[1..], WasConsumed);
        assert left + right == [left[0]] + (left[1..] + right);
        assert Seq.Partitioned([left[0]] + (left[1..] + right), WasConsumed);
        Seq.PartitionedDecomposition([left[0]], left[1..] + right, WasConsumed);
        assert Seq.Partitioned(left[1..] + right, WasConsumed);
        assert ConsumedOf(left + right) == [left[0].0] + ConsumedOf(left[1..] + right);
        assert Seq.Partitioned(left[1..] + right, WasConsumed);

        ConsumedComposition(left[1..], right);

        assert ConsumedOf(left + right) == ConsumedOf(left) + ConsumedOf(right);
      }
    }
  }

  class IgnoreNConsumer<T> extends Consumer<T> {

    const n: nat
    var consumedCount: nat

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==>
                && ValidHistory(history)
      decreases Repr, 0
    {
      && this in Repr
      && ValidHistory(history)
      && consumedCount <= n
      && (consumedCount < n ==> Seq.All(history, WasConsumed))
    }

    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()
    {}

    constructor (n: nat)
      ensures Valid()
      ensures history == []
    {
      history := [];
      Repr := {this};
      this.n := n;
      this.consumedCount := 0;
      new;
      assert ConsumedOf(history) == [];
    }

    ghost predicate ValidInput(history: seq<(T, bool)>, next: T)
      decreases Repr
    {
      true
    }

    ghost function DecreasesMetric(): TerminationMetric
      requires Valid()
      reads this, Repr
      decreases Repr, 3
    {
      TMNat(n - consumedCount)
    }

    function Capacity(): Option<nat>
      reads this, Repr
      requires Valid()
    {
      Some(n - consumedCount)
    }

    @IsolateAssertions
    method Invoke(t: T) returns (r: bool)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t), 0
      ensures Ensures(t, r)
      ensures DecreasedBy(r)
    {
      assert Requires(t);

      if consumedCount == n {
        r := false;

        UpdateHistory(t, r);
        Seq.PartitionedCompositionRight(old(history), [(t, false)], WasConsumed);
      } else {
        r := true;
        consumedCount := consumedCount + 1;

        UpdateHistory(t, r);
        Seq.PartitionedCompositionLeft(old(history), [(t, true)], WasConsumed);
      }

      ConsumedComposition(old(history), [(t, r)]);
      reveal TerminationMetric.Ordinal();
    }
  }

  @AssumeCrossModuleTermination
  class ArrayWriter<T> extends Consumer<T> {

    const storage: array<T>
    var size: nat

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==>
                && ValidHistory(history)
      decreases Repr, 0
    {
      && this in Repr
      && ValidHistory(history)
      && storage in Repr
      && size <= storage.Length
      && (Done() ==> size == storage.Length)
      && Consumed() == storage[..size]
      && (size < storage.Length ==> Seq.All(history, WasConsumed))
    }

    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()
    {}

    constructor (storage: array<T>)
      ensures Valid()
      ensures history == []
    {
      history := [];
      Repr := {this} + {storage};
      this.storage := storage;
      this.size := 0;
      new;
      assert ConsumedOf(history) == [];
      assert storage[..size] == [];
    }

    ghost predicate ValidInput(history: seq<(T, bool)>, next: T)
      decreases Repr
    {
      true
    }

    ghost function DecreasesMetric(): TerminationMetric
      requires Valid()
      reads this, Repr
      decreases Repr, 3
    {
      TMNat(storage.Length - size)
    }

    function Capacity(): Option<nat>
      reads this, Repr
      requires Valid()
    {
      Some(storage.Length - size)
    }

    @IsolateAssertions
    method Invoke(t: T) returns (r: bool)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t), 0
      ensures Ensures(t, r)
      ensures DecreasedBy(r)
    {
      assert Requires(t);

      if size == storage.Length {
        r := false;

        UpdateHistory(t, r);
        Seq.PartitionedCompositionRight(old(history), [(t, false)], WasConsumed);
      } else {
        storage[size] := t;
        size := size + 1;
        r := true;

        UpdateHistory(t, r);
        Seq.PartitionedCompositionLeft(old(history), [(t, true)], WasConsumed);
      }

      ConsumedComposition(old(history), [(t, r)]);
      reveal TerminationMetric.Ordinal();
    }
  }

  @AssumeCrossModuleTermination
  class DynamicArrayWriter<T> extends IConsumer<T>, TotalActionProof<T, ()> {

    var storage: DynamicArray<T>

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==>
                && ValidHistory(history)
      decreases Repr, 0
    {
      && this in Repr
      && storage in Repr
      && this !in storage.Repr
      && storage.Repr <= Repr
      && storage.Valid?()
      && Inputs() == storage.items
    }

    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()
    {}

    constructor ()
      ensures Valid()
      ensures fresh(Repr - {this})
      ensures history == []
    {
      var a := new DynamicArray();

      history := [];
      Repr := {this} + {a} + a.Repr;
      this.storage := a;
    }

    ghost predicate ValidHistory(history: seq<(T, ())>)
      decreases Repr
    {
      true
    }
    ghost predicate ValidInput(history: seq<(T, ())>, next: T)
      decreases Repr
    {
      true
    }

    ghost function Decreases(t: T): ORDINAL
      reads Reads(t)
    {
      0
    }

    method Invoke(t: T) returns (r: ())
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t), 0
      ensures Ensures(t, r)
    {
      assert Requires(t);

      assert Inputs() == storage.items;
      storage.Push(t);

      r := ();
      UpdateHistory(t, r);
      Repr := {this} + {storage} + storage.Repr;
      assert Inputs() == old(Inputs()) + [t];
      assert Valid();
    }

    ghost function Action(): Action<T, ()> {
      this
    }

    lemma AnyInputIsValid(history: seq<(T, ())>, next: T)
      requires Action().ValidHistory(history)
      ensures Action().ValidInput(history, next)
    {}
  }

  class FoldingConsumer<T, R> extends IConsumer<T> {

    ghost const init: R
    const f: (R, T) -> R
    var value: R

    constructor(init: R, f: (R, T) -> R)
      ensures Valid()
      ensures fresh(Repr)
    {
      this.init := init;
      this.f := f;
      this.value := init;
      this.Repr := {this};
      this.history := [];
      new;
      reveal Seq.FoldLeft();
      assert value == Seq.FoldLeft(f, init, Inputs());
    }

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==>
                && ValidHistory(history)
      decreases Repr, 0
    {
      && this in Repr
      && value == Seq.FoldLeft(f, init, Inputs())
    }

    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()
    {}

    ghost predicate ValidHistory(history: seq<(T, ())>)
      decreases Repr
    {
      true
    }
    ghost predicate ValidInput(history: seq<(T, ())>, next: T)
      decreases Repr
    {
      true
    }

    ghost function Decreases(t: T): ORDINAL
      reads Reads(t)
    {
      0
    }

    method Invoke(t: T) returns (r: ())
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t), 0
      ensures Ensures(t, r)
    {
      assert Requires(t);

      value := f(value, t);
      r := ();
      UpdateHistory(t, ());

      assert old(value) == Seq.FoldLeft(f, init, old(Inputs()));
      assert Inputs() == old(Inputs()) + [t];
      reveal Seq.FoldLeft();
      Seq.LemmaFoldLeftDistributesOverConcat(f, init, old(Inputs()), [t]);
      assert value == Seq.FoldLeft(f, init, Inputs());
      assert Valid();
    }

    ghost function Action(): Action<T, ()> {
      this
    }

    lemma AnyInputIsValid(history: seq<(T, ())>, next: T)
      requires Action().ValidHistory(history)
      ensures Action().ValidInput(history, next)
    {}
  }

  @AssumeCrossModuleTermination
  class FoldingConsumerTotalActionProof<I, O> extends TotalActionProof<I, ()> {

    ghost const action: FoldingConsumer<I, O>

    constructor (action: FoldingConsumer<I, O>)
      ensures Valid()
      ensures fresh(Repr)
      ensures Action() == action
    {
      this.action := action;
      this.Repr := {this};
    }

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr, 0
    {
      this in Repr
    }

    twostate predicate ValidChange()
      reads this, Repr
      ensures ValidChange() ==>
                old(Valid()) && Valid() && fresh(Repr - old(Repr))
      decreases Repr, 0
    {
      old(Valid()) && Valid() && fresh(Repr - old(Repr))
    }

    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()
    {}

    ghost function Action(): Action<I, ()> {
      action
    }

    lemma AnyInputIsValid(history: seq<(I, ())>, next: I)
      requires Action().ValidHistory(history)
      ensures Action().ValidInput(history, next)
    {}
  }

  @AssumeCrossModuleTermination
  class SeqWriter<T> extends IConsumer<T> {

    var values: seq<T>

    constructor ()
      reads {}
      ensures Valid()
      ensures fresh(Repr)
      ensures history == []
    {
      values := [];
      history := [];
      Repr := {this};
    }

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases Repr, 0
    {
      && this in Repr
      && values == Inputs()
    }

    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()
    {}

    ghost predicate ValidHistory(history: seq<(T, ())>)
      decreases Repr
    {
      true
    }
    ghost predicate ValidInput(history: seq<(T, ())>, next: T)
      requires ValidHistory(history)
      decreases Repr
    {
      true
    }

    ghost function Decreases(t: T): ORDINAL
      reads Reads(t)
    {
      0
    }

    method Invoke(t: T) returns (r: ())
      requires Requires(t)
      reads Repr
      modifies Modifies(t)
      decreases Decreases(t), 0
      ensures Ensures(t, r)
    {
      values := values + [t];
      r := ();

      UpdateHistory(t, r);
      assert Valid();
    }

    ghost method totalActionProof() returns (p: TotalActionProof<T, ()>)
      reads {}
      ensures p.Valid()
      ensures fresh(p.Repr)
      ensures p.Action() == this
    {
      p := new SeqWriterTotalActionProof(this);
    }
  }

  @AssumeCrossModuleTermination
  class SeqWriterTotalActionProof<T> extends TotalActionProof<T, ()> {

    ghost const action: SeqWriter<T>

    ghost constructor (action: SeqWriter<T>)
      reads {}
      ensures Valid()
      ensures fresh(Repr)
      ensures Action() == action
    {
      this.action := action;
      this.Repr := {this};
    }

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr, 0
    {
      this in Repr
    }

    twostate predicate ValidChange()
      reads this, Repr
      ensures ValidChange() ==>
                old(Valid()) && Valid() && fresh(Repr - old(Repr))
      decreases Repr, 0
    {
      old(Valid()) && Valid() && fresh(Repr - old(Repr))
    }

    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()
    {}

    ghost function Action(): Action<T, ()> {
      action
    }

    lemma AnyInputIsValid(history: seq<(T, ())>, next: T)
      requires Action().ValidHistory(history)
      ensures Action().ValidInput(history, next)
    {}
  }
}