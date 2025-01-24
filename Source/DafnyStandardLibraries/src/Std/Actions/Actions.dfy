/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Std.Actions {

  import opened Wrappers
  import opened Frames
  import opened GenericActions
  import opened Termination
  import opened DynamicArray
  import opened Math
  import Collections.Seq

  // A composable imperative action.
  //
  // Specializes GenericAction to assume its behavior can be specified
  // independently from most other actions,
  // and therefore fits into the Valid()/Repr idiom
  // (and hence extends the Validatable trait).
  // Its specified behavior is allowed to depend on only
  // what inputs it consumed and outputs it produced in the past.
  // 
  // A key design point for making this possible in Dafny:
  // the CanConsume and CanProduce predicates,
  // which the action's specification of behavior are drawn from,
  // specifically avoid reading the current state of the action.
  // That is so extrisnic properties of an action do NOT depend on their current state.
  // This is key to ensure that you can prove properties of a given action that
  // will continue to hold as the Dafny heap changes.
  // This approach works because Dafny understands that for a given object,
  // the implementation of CanConsume/CanProduce cannot change over time.
  //
  // The downside is that these are then forced to use quantifiers
  // to talk about all possible states of an action.
  // The solution is the trait proof pattern,
  // where a trait is passed around with an abstract lemma
  // that can be invoked on the otherwise quantified state as needed.
  // TODO: see (somewhere I can talk about that pattern more generally)
  //
  // This trait is intended to be applicable for any imperative action
  // regardless of how many input or output values it consumes and produces,
  // despite only defining two type parameters.
  // Implementors should feel free to use the () unit type or tuple types
  // for T and R, under the assumption that
  // future Dafny backends will be able to easily optimize
  // away the overhead of passing around a pointless () value
  // or wrapping up multiple values into a tuple.
  //
  // TODO: Better type parameter names for T and R?
  // 
  @AssumeCrossModuleTermination
  trait Action<T, R> extends GenericAction<T, R>, Validatable {

    ghost var history: seq<(T, R)>

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> CanProduce(history)
      decreases height, 0


    ghost predicate CanConsume(history: seq<(T, R)>, next: T)
      requires CanProduce(history)
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

    // Possibly optimized extensions

    // Equivalent to DefaultRepeatUntil below, but may be implemented more efficiently.
    method RepeatUntil(t: T, stop: R -> bool, ghost eventuallyStopsProof: ProducesTerminatedProof<T, R>)
      requires Valid()
      requires eventuallyStopsProof.Action() == this
      requires eventuallyStopsProof.FixedInput() == t
      requires eventuallyStopsProof.StopFn() == stop
      requires forall i <- Consumed() :: i == t
      reads Repr
      modifies Repr
      decreases Repr
      ensures Valid()
    //ensures history == old(history) + (n copies of t)/(n - 1 not stop values + stop)

    // Convenience methods for specifications

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

  method DefaultRepeatUntil<T, R>(a: Action<T, R>, t: T, stop: R -> bool, ghost eventuallyStopsProof: ProducesTerminatedProof<T, R>)
    requires a.Valid()
    requires eventuallyStopsProof.Action() == a
    requires eventuallyStopsProof.FixedInput() == t
    requires eventuallyStopsProof.StopFn() == stop
    requires forall i <- a.Consumed() :: i == t
    reads a.Repr
    modifies a.Repr
    ensures a.Valid()
  {
    while (true)
      modifies a.Repr
      invariant fresh(a.Repr - old(a.Repr))
      invariant a.Valid()
      invariant forall i <- a.Consumed() :: i == t
      decreases eventuallyStopsProof.Remaining()
    {
      label beforeInvoke:
      assert a.Valid();
      assert a.CanProduce(a.history);
      eventuallyStopsProof.CanConsumeAll(a.history, t);
      assert a.CanConsume(a.history, t);
      var next := a.Invoke(t);
      var nextV := next;
      if stop(nextV) {
        break;
      }
      eventuallyStopsProof.InvokeUntilTerminationMetricDecreased@beforeInvoke(next);
    }
  }

  // Common action invariants

  function Inputs<T, R>(history: seq<(T, R)>): seq<T> {
    Seq.Map((e: (T, R)) => e.0, history)
  }

  function Outputs<T, R>(history: seq<(T, R)>): seq<R> {
    Seq.Map((e: (T, R)) => e.1, history)
  }

  // A proof that a given action accepts any T value as input,
  // independent of history.
  trait ConsumesAllProof<T, R> {
    ghost function Action(): Action<T, R>

    lemma CanConsumeAll(history: seq<(T, R)>, next: T)
      requires Action().CanProduce(history)
      ensures Action().CanConsume(history, next)
  }

  ghost predicate OnlyProduces<T, R>(i: Action<T, R>, history: seq<(T, R)>, c: R) {
    i.CanProduce(history) <==> forall e <- history :: e.1 == c
  }

  ghost predicate Terminated<T>(s: seq<T>, stop: T -> bool, n: nat) {
    forall i | 0 <= i < |s| :: n <= i <==> stop(s[i])
  }

  lemma TerminatedDistributes<T>(left: seq<T>, right: seq<T>, stop: T -> bool, n: nat)
    requires Terminated(left, stop, |left|)
    requires Terminated(right, stop, n)
    ensures Terminated(left + right, stop, |left| + n)
  {}

  lemma TerminatedUndistributes<T>(left: seq<T>, right: seq<T>, stop: T -> bool, n: nat)
    requires Terminated(left + right, stop, n)
    ensures Terminated(left, stop, n)
    ensures Terminated(right, stop, Max(0, n - |left|))
  {
    assert forall i | 0 <= i < |left| :: left[i] == (left + right)[i];
    assert forall i | 0 <= i < |right| :: right[i] == (left + right)[i + |left|];
  }

  trait ProducesTerminatedProof<T, R> extends ConsumesAllProof<T, R> {

    ghost function FixedInput(): T
    ghost function StopFn(): R -> bool
    ghost function Limit(): nat

    lemma ProducesTerminated(history: seq<(T, R)>)
      requires Action().CanProduce(history)
      requires (forall i <- Inputs(history) :: i == FixedInput())
      ensures exists n: nat | n <= Limit() :: Terminated(Outputs(history), StopFn(), n)

    // Termination metric
    ghost function Remaining(): nat
      requires Action().Valid()
      requires forall i <- Action().Consumed() :: i == FixedInput()
      reads Action().Repr
    {
      ProducesTerminated(Action().history);
      var n: nat :| n <= Limit() && Terminated(Action().Produced(), StopFn(), n);
      TerminatedDefinesNonTerminalCount(Action().Produced(), StopFn(), n);
      Limit() - NonTerminalCount(Action().Produced(), StopFn())
    }

    twostate lemma InvokeUntilTerminationMetricDecreased(new nextProduced: R)
      requires old(Action().Valid())
      requires Action().Valid()
      requires forall i <- old(Action().Consumed()) :: i == FixedInput()
      requires Action().Consumed() == old(Action().Consumed()) + [FixedInput()]
      requires Action().Produced() == old(Action().Produced()) + [nextProduced]
      requires !StopFn()(nextProduced)
      ensures Remaining() < old(Remaining())
    {
      var before := old(Action().Produced());
      var after := Action().Produced();
      ProducesTerminated(old(Action().history));
      var n: nat :| n <= Limit() && Terminated(before, StopFn(), n);
      ProducesTerminated(Action().history);
      var m: nat :| m <= Limit() && Terminated(after, StopFn(), m);
      if n < |before| {
        assert StopFn()(before[|before| - 1]);
        assert !StopFn()(Action().Produced()[|Action().Produced()| - 1]);
        assert |Action().Produced()| <= m;
        assert !StopFn()(Action().Produced()[|before| - 1]);
        assert false;
      } else {
        TerminatedDefinesNonTerminalCount(before, StopFn(), n);
        assert NonTerminalCount(before, StopFn()) <= n;
        TerminatedDistributes(before, [nextProduced], StopFn(), 1);
        assert Terminated(after, StopFn(), |after|);
        TerminatedDefinesNonTerminalCount(after, StopFn(), |after|);
      }
    }
  }

  function NonTerminalCount<T>(produced: seq<T>, stop: T -> bool): nat {
    if |produced| == 0 || stop(produced[0]) then
      0
    else
      1 + NonTerminalCount(produced[1..], stop)
  }

  lemma TerminatedDefinesNonTerminalCount<T>(s: seq<T>, stop: T -> bool, n: nat)
    requires Terminated(s, stop, n)
    ensures NonTerminalCount(s, stop) == Min(|s|, n)
  {
    if n == 0 || |s| == 0 {
    } else {
      if stop(s[0]) {
      } else {
        assert 1 <= NonTerminalCount(s, stop);
        TerminatedDefinesNonTerminalCount(s[1..], stop, n - 1);
      }
    }
  }

  class FunctionAction<T, R> extends Action<T, R> {

    // TODO: Can we support ~>?
    const f: T --> R

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==>
                && CanProduce(history)
      decreases height, 0
    {
      && this in Repr
      && CanProduce(history)
      && Produced() == Seq.MapPartialFunction(f, Consumed())
    }

    constructor(f: T -> R)
      ensures Valid()
      ensures this.f == f
      ensures fresh(Repr)
      ensures history == []
    {
      this.f := f;

      history := [];
      Repr := {this};
    }

    ghost predicate CanConsume(history: seq<(T, R)>, next: T)
      requires CanProduce(history)
      decreases height
    {
      f.requires(next)
    }
    ghost predicate CanProduce(history: seq<(T, R)>)
      decreases height
    {
      forall e <- history :: f.requires(e.0) && e.1 == f(e.0)
    }

    method {:rlimit 0} Invoke(t: T) returns (r: R)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
      ensures Ensures(t, r)
    {
      assert Requires(t);
      assert Valid();
      r := f(t);
      Update(t, r);

      calc {
        Produced();
        old(Produced()) + [r];
        old(Seq.MapPartialFunction(f, Consumed())) + [f(t)];
        Seq.MapPartialFunction(f, old(Consumed())) + [f(t)];
        Seq.MapPartialFunction(f, old(Consumed())) + Seq.MapPartialFunction(f, [t]);
        { Seq.LemmaMapPartialFunctionDistributesOverConcat(f, old(Consumed()), [t]); }
        Seq.MapPartialFunction(f, old(Consumed()) + [t]);
        Seq.MapPartialFunction(f, Consumed());
      }
      assert Valid();
    }

    method RepeatUntil(t: T, stop: R -> bool, ghost eventuallyStopsProof: ProducesTerminatedProof<T, R>)
      requires Valid()
      requires eventuallyStopsProof.Action() == this
      requires eventuallyStopsProof.FixedInput() == t
      requires eventuallyStopsProof.StopFn() == stop
      requires forall i <- Consumed() :: i == t
      reads Repr
      modifies Repr
      decreases Repr
      ensures Valid()
    {
      DefaultRepeatUntil(this, t, stop, eventuallyStopsProof);
    }
  }

  // TODO: Move to Enumerators?
  class FunctionalEnumerator<S, T> extends Action<(), Option<T>> {

    const stepFn: S -> Option<(S, T)>
    var state: S

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> CanProduce(history)
      decreases height, 0
    {
      this in Repr
    }

    constructor(state: S, stepFn: S -> Option<(S, T)>) {
      this.state := state;
      this.stepFn := stepFn;
    }

    ghost predicate CanConsume(history: seq<((), Option<T>)>, next: ())
      decreases height
    {
      true
    }
    ghost predicate CanProduce(history: seq<((), Option<T>)>)
      decreases height
    {
      true
    }

    method Invoke(t: ()) returns (r: Option<T>)
      requires Requires(t)
      reads Repr
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
      ensures Ensures(t, r)
    {
      var next := stepFn(state);
      match next {
        case Some(result) => {
          var (newState, result') := result;
          state := newState;
          r := Some(result');
        }
        case None => {
          r := None;
        }
      }
      Update(t, r);
    }

    method RepeatUntil(t: (), stop: Option<T> -> bool, ghost eventuallyStopsProof: ProducesTerminatedProof<(), Option<T>>)
      requires Valid()
      requires eventuallyStopsProof.Action() == this
      requires eventuallyStopsProof.FixedInput() == t
      requires eventuallyStopsProof.StopFn() == stop
      requires forall i <- Consumed() :: i == t
      reads Repr
      modifies Repr
      decreases Repr
      ensures Valid()
    {
      DefaultRepeatUntil(this, t, stop, eventuallyStopsProof);
    }
  }

  // A proof that a given action only produces
  // elements from a given set.
  trait ProducesSetProof<T> {
    ghost function Action(): Action<(), T>
    ghost function Set(): set<T>

    lemma ProducesSet(history: seq<((), T)>)
      requires Action().CanProduce(history)
      ensures |history| <= |Set()|
      ensures Seq.HasNoDuplicates(Outputs(history))
      ensures Seq.ToSet(Outputs(history)) <= Set()
  }

  // TODO: Rename/relocate, this isn't a finite Enumerator of Option<T>
  class SetEnumerator<T(==)> extends Action<(), T>, ProducesSetProof<T> {
    ghost const original: set<T>
    var remaining: set<T>

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> CanProduce(history)
      decreases height, 0
    {
      && this in Repr
      && CanProduce(history)
      && remaining == original - Enumerated(history)
    }

    constructor(s: set<T>)
      ensures Valid()
      ensures fresh(Repr)
      ensures history == []
      ensures s == original
    {
      original := s;
      remaining := s;

      history := [];
      Repr := {this};
      height := 1;

      reveal Seq.HasNoDuplicates();
      reveal Seq.ToSet();
    }

    ghost function Action(): Action<(), T> {
      this
    }

    ghost function Set(): set<T> {
      original
    }

    lemma ProducesSet(history: seq<((), T)>)
      requires Action().CanProduce(history)
      ensures |history| <= |Set()|
      ensures Seq.ToSet(Outputs(history)) <= Set()
    {}

    ghost function Enumerated(history: seq<((), T)>): set<T> {
      Seq.ToSet(Outputs(history))
    }

    ghost predicate CanConsume(history: seq<((), T)>, next: ())
      decreases height
    {
      |history| < |original|
    }
    ghost predicate CanProduce(history: seq<((), T)>)
      decreases height
    {
      && |history| <= |original|
      && Seq.HasNoDuplicates(Outputs(history))
      && Enumerated(history) <= original
    }

    lemma EnumeratedCardinality()
      requires Valid()
      ensures |Enumerated(history)| == |history|
    {
      reveal Seq.ToSet();
      Seq.LemmaCardinalityOfSetNoDuplicates(Outputs(history));
    }

    method Invoke(t: ()) returns (r: T)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
      ensures Ensures(t, r)
    {
      assert Requires(t);

      EnumeratedCardinality();
      assert 0 < |remaining|;

      r :| r in remaining;
      remaining := remaining - {r};

      Update(t, r);
      Repr := {this};

      assert Outputs(history) == Outputs(old(history)) + [r];
      reveal Seq.ToSet();
      assert r !in Outputs(old(history));
      reveal Seq.HasNoDuplicates();
      Seq.LemmaNoDuplicatesInConcat(Outputs(old(history)), [r]);
    }

    method RepeatUntil(t: (), stop: T -> bool, ghost eventuallyStopsProof: ProducesTerminatedProof<(), T>)
      requires Valid()
      requires eventuallyStopsProof.Action() == this
      requires eventuallyStopsProof.FixedInput() == t
      requires eventuallyStopsProof.StopFn() == stop
      requires forall i <- Consumed() :: i == t
      reads Repr
      modifies Repr
      decreases Repr
      ensures Valid()
    {
      DefaultRepeatUntil(this, t, stop, eventuallyStopsProof);
    }
  }

  // Other primitives/examples todo:
  //  * Promise-like single-use Action<T, ()> to capture a value for reading later
  //  * datatype/codatatype-based enumerations
  //  * How to state the invariant that a constructor as an action creates a new object every time?
  //    * Lemma that takes produced as input, instead of forall produced?
  //  * Expressing that an Action "Eventually produces something" (look at how VMC models this for randomness)
  //    * IsEnumerator(a) == "a eventually produces None" && "a then only produces None"
  //    * Build on that to make CrossProduct(enumerable1, enumerable2)
  //  * Example of adapting an iterator
  //  * Example of enumerating all possible values of a type (for test generation)
  //    * Needs to handle infinite types too, hence needs the "eventually produces something" concept
  //  * Document: useful pattern to add an Action<Command, Result> facade
  //        to a set of methods that participate in a protocol.
  //        Then you have a history that ties the behavior
  //        of the methods together,
  //        supporting constraints on the order of calls etc.
}