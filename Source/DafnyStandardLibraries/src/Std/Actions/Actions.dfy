
module Std.Actions {

  import opened Wrappers
  import opened Frames
  import opened Collections.Seq
  import opened Math
  import opened GenericActions
  import opened Termination

  // TODO: NOT a fully general-purpose handle on any arbitrary Dafny method,
  // because gaps in Dafny expressiveness make that impossible for now
  // (e.g. field references in framing clauses aren't expressions,
  // decreases metrics aren't directly expressible in user code)
  // Consider naming this something more specific, related to the assumptions:
  //  1. Validatable (and doesn't modify anything not in Repr)
  //  2. Behavior specified only by referring to consumed and produced.
  trait {:termination false} Action<T, R> extends GenericAction<T, R>, Validatable {

    ghost var history: seq<(T, R)>

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      ensures Valid() ==> CanProduce(history)
      decreases height, 0

    // KEY DESIGN POINT: these predicates specifically avoid reading the current
    // state of the action.
    // That's so extrisnic properties of an action do NOT depend on their current state.
    // This is key to ensure that you can prove properties of a given action that
    // will continue to hold as the Dafny heap changes.
    // This approach works because Dafny understands that for a given object,
    // the implementation of CanConsume/CanProduce cannot change over time.
    //
    // The downside is that these are then forced to use quantifiers
    // to talk about all possible states of an action.

    // TODO: Necessary but not sufficient that:
    // CanConsume(history, nextIn) ==> exists nextOut :: CanProduce(history + [(nextIn, nextOut)])
    // Does that need to be explicitly part of the spec?
    ghost predicate CanConsume(history: seq<(T, R)>, next: T)
      requires Valid()
      requires CanProduce(history)
      reads Repr
      decreases height

    ghost predicate CanProduce(history: seq<(T, R)>)
      decreases height

    ghost predicate Requires(t: T)
      reads Reads(t) 
    {
      && Valid()
      && CanConsume(history, t)
    }
    ghost function Reads(t: T): set<object> 
      reads this
      ensures this in Reads(t)
    {
      {this} + Repr
    }
    ghost function Modifies(t: T): set<object> 
      reads Reads(t)
    {
      Repr
    }
    ghost function Decreases(t: T): TerminationMetric 
      reads Reads(t)
    {
      NatTerminationMetric(height)
    }
    twostate predicate Ensures(t: T, new r: R) 
      reads Reads(t)
    {
      && Valid()
      && history == old(history) + [(t, r)]
      && fresh(Repr - old(Repr))
    }

    // Helpers

    ghost method Update(t: T, r: R)
      reads `history
      modifies `history
      ensures history == old(history) + [(t, r)]
    {
      history := history + [(t, r)];
    }

    ghost function Consumed(): seq<T> 
      reads this
    {
      Inputs(history)
    }

    ghost function Produced(): seq<R> 
      reads this
    {
      Outputs(history)
    }
  }

  // Common action invariants

  function Inputs<T, R>(history: seq<(T, R)>): seq<T> {
    Seq.Map((e: (T, R)) => e.0, history)
  }

  function Outputs<T, R>(history: seq<(T, R)>): seq<R> {
    Seq.Map((e: (T, R)) => e.1, history)
  }

  ghost predicate OnlyProduces<T, R>(i: Action<T, R>, history: seq<(T, R)>, c: R) 
  {
    i.CanProduce(history) <==> forall e <- history :: e.1 == c
  }

  ghost predicate CanConsumeAll<T(!new), R(!new)>(a: Action<T, R>, input: seq<T>) {
    forall i | 0 < i < |input| ::
      var consumed := input[..(i - 1)];
      var next := input[i];
      forall history | a.CanProduce(history) && Inputs(history) == consumed :: a.CanConsume(history, next)
  }

  ghost predicate Terminated<T>(s: seq<T>, c: T, n: nat) {
    forall i | 0 <= i < |s| :: n <= i <==> s[i] == c
  }

  lemma TerminatedUndistributes<T>(left: seq<T>, right: seq<T>, c: T, n: nat)
    requires Terminated(left + right, c, n)
    ensures Terminated(left, c, n)
    ensures Terminated(right, c, Math.Max(0, n - |left|))
  {
    assert forall i | 0 <= i < |left| :: left[i] == (left + right)[i];
    assert forall i | 0 <= i < |right| :: right[i] == (left + right)[i + |left|];
  }

  // TODO: generalize to "EventuallyProducesSequence"?
  ghost predicate ProducesTerminatedBy<T(!new), R(!new)>(i: Action<T, R>, c: R, limit: nat) {
    forall history: seq<(T, R)> | i.CanProduce(history) 
      :: exists n: nat | n <= limit :: Terminated(Outputs(history), c, n)
  }

  // Class of actions whose precondition doesn't depend on history (probably needs a better name)
  ghost predicate ContextFree<T(!new), R(!new)>(a: Action<T, R>, p: T -> bool) {
    forall history, next | a.CanProduce(history)
      :: a.CanConsume(history, next) <==> p(next)
  }

  // Aggregators

  type IAggregator<T> = Action<T, ()>
  type Aggregator<T(!new)> = a: Action<T, bool> | exists limit :: ProducesTerminatedBy(a, false, limit) witness *

  // TODO: Refactor to use DynamicArray
  class ArrayAggregator<T(0)> extends Action<T, ()> {

    var storage: array<T>
    var index: nat

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      ensures Valid() ==> 
        && CanProduce(history)
      decreases height, 0
    {
      && this in Repr
      && storage in Repr
      && 0 < storage.Length
      && 0 <= index <= storage.Length
      && Consumed() == storage[..index]
    }

    constructor() 
      ensures Valid()
      ensures fresh(Repr - {this})
      ensures history == []
    {
      index := 0;
      storage := new T[10];

      history := [];
      Repr := {this, storage};
    }

    ghost predicate CanConsume(history: seq<(T, ())>, next: T)
      decreases height
    {
      true
    }
    ghost predicate CanProduce(history: seq<(T, ())>)
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
      if index == storage.Length {
        var newStorage := new T[storage.Length * 2];
        forall i | 0 <= i < index {
          newStorage[i] := storage[i];
        }
        storage := newStorage;

        Repr := {this, storage};
      }
      storage[index] := t;
      index := index + 1;

      r := ();
      Update(t, r);
      assert Valid();
    }

    function Values(): seq<T>
      requires Valid()
      reads Repr
      ensures Values() == Consumed()
    {
      storage[..index]
    }
  }

  method AggregatorExample() {
    var a := new ArrayAggregator();
    var _ := a.Invoke(1);
    var _ := a.Invoke(2);
    var _ := a.Invoke(3);
    var _ := a.Invoke(4);
    var _ := a.Invoke(5);
    assert a.Values() == [1, 2, 3, 4, 5];
  }

  // Other primitives/examples todo:
  //  * Promise-like single-use Action<T, ()> to capture a value for reading later
  //  * Eliminate all the (!new) restrictions - look into "older" parameters?
  //    * How to state the invariant that a constructor as an action creates a new object every time?
  //      * Lemma that takes produced as input, instead of forall produced?
  //  * Enumerable ==> defines e.Enumerator()
  //    * BUT can have infinite containers, probably need IEnumerable as well? (different T for the Action)
  //  * Expressing that an Action "Eventually produces something" (look at how VMC models this for randomness)
  //    * IsEnumerator(a) == "a eventually produces None" && "a then only produces None"
  //    * Build on that to make CrossProduct(enumerable1, enumerable2)
  //  * Example of adapting an iterator
  //  * Example of enumerating all possible values of a type (for test generation)
  //    * Needs to handle infinite types too, hence needs the "eventually produces something" concept

}