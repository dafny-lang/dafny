/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Std.Aggregators {

  import opened Actions
  import opened Wrappers
  import opened DynamicArray
  import Collections.Seq

  // TODO: Not 100% confident in the exact name and signature here:
  // * As per the module name, I think I like "Aggregator" as the dual to "Enumerator" better
  // * This signature is not a complete dual of Enumerator: an Enumerator is a finite enumeration,
  //   and one where the number of elements isn't statically known
  //   (returns an Option<T> rather than a T). A dual to that concept should also be allowed
  //   to accept only a finite number of elements, so it should probably return a boolean.
  //   This would be the kind of Action that writes element in sequence into a fixed-length array,
  //   for example, and therefore has finite capacity.
  //   
  //   Perhaps we should have:
  //     - IProducer = Action<(), T> (potentially infinite elements)
  //     - Producer = Action<(), Option<T>> + proofs of eventually producing None (finite elements)
  //     - IConsumer = Action<T, ()> (potentially infinite elements)
  //     - Consumer = Action<T, boolean> + proofs of eventually producing false (finite elements)
  //
  //   It may make sense to have more than one ForEach as well: 
  //   one that connects an IProducer and an IConsumer together and runs forever (decreases *),
  //   one that connects an Producer and an Consumer with a proof that the aggregator has adequate capacity,
  //   and one that connects an Producer and an IConsumer with no additional proof obligation.
  @AssumeCrossModuleTermination
  trait Accumulator<T> extends Action<T, ()>, TotalActionProof<T, ()> {

    ghost function Action(): Action<T, ()> {
      this
    }

    // For better readability
    method Accept(t: T)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      ensures Ensures(t, ())
    {
      assert Requires(t);

      AnyInputIsValid(history, t);
      var r := Invoke(t);
      assert r == ();
    }
  }

  @AssumeCrossModuleTermination
  class ArrayAggregator<T> extends Action<T, bool> {

    var storage: array<T>
    var size: nat

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==>
                && ValidHistory(history)
      decreases height, 0
    {
      && this in Repr
      && storage in Repr
      && size <= storage.Length
      && Inputs() == storage[..size]
    }

    constructor (storage: array<T>)
      ensures Valid()
      ensures history == []
    {
      history := [];
      height := 1;
      Repr := {this} + {storage};
      this.storage := storage;
      this.size := 0;
    }

    ghost predicate ValidInput(history: seq<(T, bool)>, next: T)
      decreases height
    {
      true
    }
    ghost predicate ValidHistory(history: seq<(T, bool)>)
      decreases height
    {
      true
    }

    method Invoke(t: T) returns (r: bool)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
      ensures Ensures(t, r)
    {
      assert Requires(t);

      if size == storage.Length {
        r := false;
      } else {
        storage[size] := t;
        size := size + 1;
        r := true;
      }

      UpdateHistory(t, r);
      Repr := {this} + {storage};
      assert Inputs() == old(Inputs()) + [t];
      assume {:axiom} Valid();
    }

    method RepeatUntil(t: T, stop: bool -> bool, ghost eventuallyStopsProof: ProducesTerminatedProof<T, bool>)
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
  }

  class DynamicArrayAggregator<T> extends Accumulator<T> {

    var storage: DynamicArray<T>

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==>
                && ValidHistory(history)
      decreases height, 0
    {
      && this in Repr
      && storage in Repr
      && this !in storage.Repr
      && storage.Repr <= Repr
      && storage.Valid?()
      && Inputs() == storage.items
    }

    constructor ()
      ensures Valid()
      ensures fresh(Repr - {this})
      ensures history == []
    {
      var a := new DynamicArray();

      history := [];
      height := 1;
      Repr := {this} + {a} + a.Repr;
      this.storage := a;
    }

    ghost predicate ValidInput(history: seq<(T, ())>, next: T)
      decreases height
    {
      true
    }
    ghost predicate ValidHistory(history: seq<(T, ())>)
      decreases height
    {
      true
    }

    method Invoke(t: T) returns (r: ())
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
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

    method RepeatUntil(t: T, stop: (()) -> bool, ghost eventuallyStopsProof: ProducesTerminatedProof<T, ()>)
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

    lemma AnyInputIsValid(history: seq<(T, ())>, next: T)
      requires Action().ValidHistory(history)
      ensures Action().ValidInput(history, next)
    {}
  }

  class FoldingAccumulator<T, R> extends Accumulator<T> {

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
      decreases height, 0
    {
      && this in Repr
      && value == Seq.FoldLeft(f, init, Inputs())
    }

    ghost predicate ValidInput(history: seq<(T, ())>, next: T)
      decreases height
    {
      true
    }
    ghost predicate ValidHistory(history: seq<(T, ())>)
      decreases height
    {
      true
    }

    method Invoke(t: T) returns (r: ())
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
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

    method RepeatUntil(t: T, stop: (()) -> bool, ghost eventuallyStopsProof: ProducesTerminatedProof<T, ()>)
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

    lemma AnyInputIsValid(history: seq<(T, ())>, next: T)
      requires Action().ValidHistory(history)
      ensures Action().ValidInput(history, next)
    {}
  }

  // TODO: This is also a FoldingAccumulator([], (x, y) => x + [y])
  class Collector<T> extends Accumulator<T> {

    var values: seq<T>

    constructor ()
      ensures Valid()
      ensures fresh(Repr)
    {
      values := [];
      history := [];
      Repr := {this};
    }

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases height, 0
    {
      this in Repr
    }

    ghost predicate ValidInput(history: seq<(T, ())>, next: T)
      requires ValidHistory(history)
      decreases height
    {
      true
    }

    ghost predicate ValidHistory(history: seq<(T, ())>)
      decreases height
    {
      true
    }

    method Invoke(t: T) returns (r: ())
      requires Requires(t)
      reads Repr
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
      ensures Ensures(t, r)
    {
      values := values + [t];
      r := ();

      UpdateHistory(t, r);
      assert Valid();
    }

    method RepeatUntil(t: T, stop: (()) -> bool, ghost eventuallyStopsProof: ProducesTerminatedProof<T, ()>)
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

    method Pop() returns (t: T)
      requires Valid()
      requires 0 < |values|
      reads Repr
      modifies Repr
      ensures Valid()
    {
      t := values[0];
      values := values[1..];
    }

    lemma AnyInputIsValid(history: seq<(T, ())>, next: T)
      requires Action().ValidHistory(history)
      ensures Action().ValidInput(history, next)
    {}
  }
}