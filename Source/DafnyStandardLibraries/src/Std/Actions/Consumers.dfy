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

  // Actions that attempt to consume a T and eventually reach capacity and fail.
  @AssumeCrossModuleTermination
  trait Consumer<T> extends Action<T, bool> {

    // Termination metric ensuring Accept() eventually returns false.
    // Not necessarily an exact measurement of the capacity remaining,
    // only a conservative bound.
    ghost function RemainingMetric(): TerminationMetric
      requires Valid()
      reads this, Repr
      decreases Repr, 3

    ghost function Remaining(): ORDINAL
      requires Valid()
      reads this, Repr
    {
      RemainingMetric().Ordinal()
    }

    twostate predicate RemainingDecreasedBy(new result: bool)
      requires old(Valid())
      requires Valid()
      reads this, Repr
    {
      if result then
        old(RemainingMetric()).DecreasesTo(RemainingMetric())
      else
        old(RemainingMetric()).NonIncreasesTo(RemainingMetric())
    }

    ghost function Decreases(t: T): ORDINAL
      requires Requires(t)
      reads Reads(t)
    {
      Remaining()
    }

    method Invoke(t: T) returns (r: bool)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t), 0
      ensures Ensures(t, r)
      ensures RemainingDecreasedBy(r)

    // For better readability
    method Accept(t: T) returns (o: bool)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t), 0
      ensures Ensures(t, o)
      ensures RemainingDecreasedBy(o)
    {
      assert Requires(t);

      o := Invoke(t);
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
      && storage in Repr
      && size <= storage.Length
      && Inputs() == storage[..size]
    }

    constructor (storage: array<T>)
      ensures Valid()
      ensures history == []
    {
      history := [];
      Repr := {this} + {storage};
      this.storage := storage;
      this.size := 0;
    }

    ghost predicate ValidHistory(history: seq<(T, bool)>)
      decreases Repr
    {
      |history| <= storage.Length
    }
    ghost predicate ValidInput(history: seq<(T, bool)>, next: T)
      decreases Repr
    {
      |history| < storage.Length
    }

    ghost function RemainingMetric(): TerminationMetric
      requires Valid()
      reads this, Repr
      decreases Repr, 3
    {
      TMNat(storage.Length - size)
    }

    method Invoke(t: T) returns (r: bool)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t), 0
      ensures Ensures(t, r)
      ensures RemainingDecreasedBy(r)
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
      assert Valid();
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
  class SeqWriter<T> extends IConsumer<T>, TotalActionProof<T, ()> {

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
      decreases Repr, 0
    {
      this in Repr
    }

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

    ghost function Action(): Action<T, ()> {
      this
    }

    lemma AnyInputIsValid(history: seq<(T, ())>, next: T)
      requires Action().ValidHistory(history)
      ensures Action().ValidInput(history, next)
    {}
  }
}