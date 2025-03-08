/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Std.Consumers {

  import opened Actions
  import opened Wrappers
  import opened DynamicArray
  import Collections.Seq

  @AssumeCrossModuleTermination
  trait IConsumer<T> extends Action<T, ()> {

    // For better readability
    method Accept(t: T)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      ensures Ensures(t, ())
    {
      assert Requires(t);

      var r := Invoke(t);
      assert r == ();
    }
  }

  @AssumeCrossModuleTermination
  trait Consumer<T> extends Action<T, bool> {

    ghost function Action(): Action<T, bool> {
      this
    }

    // For better readability
    method Accept(t: T)
      returns (o: bool)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      ensures Ensures(t, o)
    {
      assert Requires(t);

      o := Invoke(t);
    }
  }

  // TODO: Name implies it's consuming arrays
  @AssumeCrossModuleTermination
  class ArrayConsumer<T> extends Consumer<T> {

    const storage: array<T>
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

    ghost predicate ValidHistory(history: seq<(T, bool)>)
      decreases height
    {
      |history| <= storage.Length
    }
    ghost predicate ValidInput(history: seq<(T, bool)>, next: T)
      decreases height
    {
      |history| < storage.Length
    }
    twostate predicate ValidOutput(history: seq<(T, bool)>, nextInput: T, new nextOutput: bool)
      decreases height
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)])
    }

    method Invoke(t: T) returns (r: bool)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal(), 0
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
      assert Valid();
    }
  }

  @AssumeCrossModuleTermination
  class DynamicArrayConsumer<T> extends IConsumer<T>, TotalActionProof<T, ()> {

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

    ghost predicate ValidHistory(history: seq<(T, ())>)
      decreases height
    {
      true
    }
    ghost predicate ValidInput(history: seq<(T, ())>, next: T)
      decreases height
    {
      true
    }
    twostate predicate ValidOutput(history: seq<(T, ())>, nextInput: T, new nextOutput: ())
      decreases height
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)])
    }

    method Invoke(t: T) returns (r: ())
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal(), 0
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
      this.height := 0;
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

    ghost predicate ValidHistory(history: seq<(T, ())>)
      decreases height
    {
      true
    }
    ghost predicate ValidInput(history: seq<(T, ())>, next: T)
      decreases height
    {
      true
    }
    twostate predicate ValidOutput(history: seq<(T, ())>, nextInput: T, new nextOutput: ())
      decreases height
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)])
    }

    method Invoke(t: T) returns (r: ())
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal(), 0
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

  // TODO: This is also a FoldingConsumer([], (x, y) => x + [y])
  // Or a SeqConsumer?
  @AssumeCrossModuleTermination
  class Collector<T> extends IConsumer<T>, TotalActionProof<T, ()> {

    var values: seq<T>

    constructor ()
      ensures Valid()
      ensures fresh(Repr)
    {
      values := [];
      history := [];
      Repr := {this};
      height := 0;
    }

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases height, 0
    {
      this in Repr
    }

    ghost predicate ValidHistory(history: seq<(T, ())>)
      decreases height
    {
      true
    }
    ghost predicate ValidInput(history: seq<(T, ())>, next: T)
      requires ValidHistory(history)
      decreases height
    {
      true
    }
    twostate predicate ValidOutput(history: seq<(T, ())>, nextInput: T, new nextOutput: ())
      decreases height
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)])
    }

    method Invoke(t: T) returns (r: ())
      requires Requires(t)
      reads Repr
      modifies Modifies(t)
      decreases Decreases(t).Ordinal(), 0
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