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

  // Actions that attempt to consume a T and eventually reach capacity and fail.
  @AssumeCrossModuleTermination
  trait Consumer<T> extends Action<T, bool> {

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
      !Seq.All(Outputs(), IsFalse)
    }

    function Capacity(): Option<nat>
      reads this, Repr
      requires Valid()

    // ghost function Consumed(): seq<T> {
    //   Seq.Count(IsTrue, Outputs())
    // }

    // twostate function NewConsumed(): seq<T> {
    //   Consumed() - old(Consumed())
    // }

    // twostate lemma CapacityCorrect()
    //   requires ValidChange()
    //   requires old(Capacity()).Some?
    //   ensures |NewConsumed()| < old(Capacity()).value
    //   ensures Done() ==> |NewConsumed()| == old(Capacity()).value

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
    }

    ghost predicate ValidHistory(history: seq<(T, bool)>)
      decreases Repr
    {
      true
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
      ensures ValidChange() ==> old(Valid()) && Valid()
      decreases Repr, 0
    {
      old(Valid()) && Valid()
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

    method totalActionProof() returns (p: TotalActionProof<T, ()>)
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

    constructor (action: SeqWriter<T>)
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
      ensures ValidChange() ==> old(Valid()) && Valid()
      decreases Repr, 0
    {
      old(Valid()) && Valid()
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