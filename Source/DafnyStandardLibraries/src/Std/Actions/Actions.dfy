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

  //
  // A composable imperative action.
  //
  // See https://github.com/dafny-lang/dafny/blob/master/Source/DafnyStandardLibraries/src/Std/Actions/Actions.md
  // for further details.
  //
  @AssumeCrossModuleTermination
  trait Action<I, O> extends GenericAction<I, O>, Validatable {

    ghost var history: seq<(I, O)>

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases Repr, 0

    ghost predicate ValidHistory(history: seq<(I, O)>)
      decreases Repr

    ghost predicate ValidInput(history: seq<(I, O)>, next: I)
      requires ValidHistory(history)
      decreases Repr

    ghost predicate Requires(i: I)
      reads Reads(i)
    {
      && Valid()
      && ValidInput(history, i)
    }
    ghost function Reads(i: I): set<object>
      reads this
      ensures this in Reads(i)
    {
      {this} + Repr
    }
    ghost function Modifies(i: I): set<object>
      reads Reads(i)
    {
      Repr
    }
    twostate predicate Ensures(i: I, new o: O)
      requires old(Requires(i))
      reads Reads(i)
    {
      && ValidAndDisjoint()
      && history == old(history) + [(i, o)]
    }

    // Convenience methods for specifications

    ghost method UpdateHistory(i: I, o: O)
      reads `history
      modifies `history
      ensures history == old(history) + [(i, o)]
    {
      history := history + [(i, o)];
    }

    ghost function Inputs(): seq<I>
      reads this
    {
      InputsOf(history)
    }

    ghost function Outputs(): seq<O>
      reads this
    {
      OutputsOf(history)
    }
  }

  function InputsOf<I, O>(history: seq<(I, O)>): seq<I> {
    Seq.Map((e: (I, O)) => e.0, history)
  }

  function OutputsOf<I, O>(history: seq<(I, O)>): seq<O> {
    Seq.Map((e: (I, O)) => e.1, history)
  }

  // A proof that a given action accepts any I value as input,
  // independent of history.
  //
  // This is an example of the "proof trait" pattern:
  // a trait that defines one or more lemmas to be filled in by extenders.
  // They are used to work around the fact that Dafny does not allow
  // quantification that depends on the set of allocated references
  // in many contexts.
  // Without that restriction, we could use the following predicate:
  //
  //   forall history: seq<(I, O)>, input: I | action.ValidHistory(history) :: action.ValidInput(history, input)
  // 
  // But this is rejected in predicates unless I and O are declared with (!new),
  // which greatly restricts the utility of code that needs to work with reference types.
  // Instead the AnyInputIsValid lemma below takes the quantified variables as input,
  // and has to prove the postcondition holds for any arbitrary values that satsify the precondition.
  // 
  // Code that depends on this property then accepts a ghost value that implements the trait
  // and explicitly applies the lemma on inputs at hand as needed.
  // As a side effect, this can result in less brittle verification,
  // since unlike quantifiers, proof traits are only manually triggered as needed.
  //
  // For cases where it IS reasonable to restrict type parameters to non-reference types,
  // default implementations of the proof trait are often provided
  // that rely on quantifiers.
  // See DefaultTotalActionProof below for example.
  @AssumeCrossModuleTermination
  trait TotalActionProof<I, O> extends Validatable {
    ghost function Action(): Action<I, O>

    lemma AnyInputIsValid(history: seq<(I, O)>, next: I)
      requires Valid()
      requires Action().ValidHistory(history)
      ensures Action().ValidInput(history, next)
  }

  // A simple proof of an action being total.
  // Relies on quantifiers so it only works for non-reference types.
  @AssumeCrossModuleTermination
  class DefaultTotalActionProof<I(!new), O(!new)> extends TotalActionProof<I, O> {

    const action: Action<I, O>

    ghost constructor(action: Action<I, O>)
      requires action.Valid()
      requires forall history: seq<(I, O)>, input: I | action.ValidHistory(history) :: action.ValidInput(history, input)
      ensures this.action == action
      ensures Valid()
      ensures fresh(Repr)
    {
      this.action := action;
      Repr := {this};
    }

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr, 0
    {
      && Repr == {this}
      && forall history: seq<(I, O)>, input: I | action.ValidHistory(history) :: action.ValidInput(history, input)
    }

    ghost function Action(): Action<I, O> {
      action
    }

    lemma AnyInputIsValid(history: seq<(I, O)>, next: I)
      requires Valid()
      requires Action().ValidHistory(history)
      ensures Action().ValidInput(history, next)
    {}
  }

  ghost predicate OnlyOutputs<I, O>(i: Action<I, O>, history: seq<(I, O)>, c: O) {
    i.ValidHistory(history) <==> forall e <- history :: e.1 == c
  }

  class FunctionAction<I, O> extends Action<I, O> {

    const f: I --> O

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==>
                && ValidHistory(history)
      decreases Repr, 0
    {
      && this in Repr
      && ValidHistory(history)
      && Outputs() == Seq.MapPartialFunction(f, Inputs())
    }

    constructor(f: I -> O)
      ensures Valid()
      ensures this.f == f
      ensures fresh(Repr)
      ensures history == []
    {
      this.f := f;

      history := [];
      Repr := {this};
    }

    ghost predicate ValidHistory(history: seq<(I, O)>)
      decreases Repr
    {
      forall e <- history :: f.requires(e.0) && e.1 == f(e.0)
    }
    ghost predicate ValidInput(history: seq<(I, O)>, next: I)
      requires ValidHistory(history)
      decreases Repr
    {
      f.requires(next)
    }

    ghost function Decreases(i: I): ORDINAL
      reads Reads(i)
    {
      0
    }

    method Invoke(i: I) returns (o: O)
      requires Requires(i)
      reads Reads(i)
      modifies Modifies(i)
      decreases Decreases(i), 0
      ensures Ensures(i, o)
    {
      assert Requires(i);
      assert Valid();
      o := f(i);
      UpdateHistory(i, o);

      calc {
        Outputs();
        old(Outputs()) + [o];
        old(Seq.MapPartialFunction(f, Inputs())) + [f(i)];
        Seq.MapPartialFunction(f, old(Inputs())) + [f(i)];
        Seq.MapPartialFunction(f, old(Inputs())) + Seq.MapPartialFunction(f, [i]);
        { Seq.LemmaMapPartialFunctionDistributesOverConcat(f, old(Inputs()), [i]); }
        Seq.MapPartialFunction(f, old(Inputs()) + [i]);
        Seq.MapPartialFunction(f, Inputs());
      }
      assert Valid();
    }
  }

  class ComposedAction<I, M, O> extends Action<I, O> {

    const first: Action<I, M>
    const second: Action<M, O>

    ghost const compositionProof: ActionCompositionProof<I, M, O>

    constructor(first: Action<I, M>, second: Action<M, O>, ghost compositionProof: ActionCompositionProof<I, M, O>)
      requires first.Valid()
      requires first.history == []
      requires second.Valid()
      requires second.history == []
      requires first.Repr !! second.Repr
      requires compositionProof.FirstAction() == first
      requires compositionProof.SecondAction() == second
      ensures Valid()
      ensures history == []
      ensures this.compositionProof == compositionProof
    {
      this.first := first;
      this.second := second;
      this.compositionProof := compositionProof;

      history := [];
      Repr := {this} + first.Repr + second.Repr;
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
      && ValidHistory(history)
      && InputsOf(history) == InputsOf(first.history)
      && OutputsOf(first.history) == InputsOf(second.history)
      && OutputsOf(second.history) == OutputsOf(history)
      && compositionProof.FirstAction() == first
      && compositionProof.SecondAction() == second
    }

    ghost predicate ValidHistory(history: seq<(I, O)>)
      decreases Repr
    {
      compositionProof.ComposedValidHistory(history)
    }
    ghost predicate ValidInput(history: seq<(I, O)>, next: I)
      decreases Repr
    {
      compositionProof.ComposedValidInput(history, next)
    }

    ghost function Decreases(i: I): ORDINAL
      reads Reads(i)
    {
      ReprTerminationMetric().Ordinal()
    }

    @IsolateAssertions
    @ResourceLimit("0")
    method Invoke(i: I) returns (o: O)
      requires Requires(i)
      reads Reads(i)
      modifies Modifies(i)
      decreases Decreases(i), 0
      ensures Ensures(i, o)
    {
      assert Requires(i);

      assert first.Valid();
      assert first.ValidHistory(first.history);
      compositionProof.CanInvokeFirst(first.history, history, i);
      var m := first.Invoke(i);

      assert second.Valid();
      compositionProof.CanInvokeSecond(second.history, history, i, m);
      o := second.Invoke(m);

      UpdateHistory(i, o);
      Repr := {this} + first.Repr + second.Repr;

      assert InputsOf(history) == old(InputsOf(first.history)) + [i];
      assert InputsOf(history) == InputsOf(first.history);

      assert OutputsOf(first.history) == old(OutputsOf(first.history)) + [m];
      assert InputsOf(second.history) == old(InputsOf(second.history)) + [m];
      assert OutputsOf(first.history) == InputsOf(second.history);

      assert OutputsOf(history) == old(OutputsOf(second.history)) + [o];
      assert OutputsOf(second.history) == OutputsOf(history);

      compositionProof.CanReturn(first.history, second.history, history);

      assert history == old(history) + [(i, o)];
      assert compositionProof.ComposedValidHistory(history);
      assert ValidHistory(history);
    }
  }

  trait ActionCompositionProof<I, M, O> {
    ghost function FirstAction(): Action<I, M>
    ghost function SecondAction(): Action<M, O>

    ghost predicate ComposedValidInput(composedHistory: seq<(I, O)>, next: I)

    lemma CanInvokeFirst(firstHistory: seq<(I, M)>, composedHistory: seq<(I, O)>, next: I)
      requires FirstAction().ValidHistory(firstHistory)
      requires ComposedValidInput(composedHistory, next)
      requires InputsOf(firstHistory) == InputsOf(composedHistory)
      ensures FirstAction().ValidInput(firstHistory, next)

    lemma CanInvokeSecond(secondHistory: seq<(M, O)>, composedHistory: seq<(I, O)>, nextT: I, nextM: M)
      requires SecondAction().ValidHistory(secondHistory)
      requires OutputsOf(secondHistory) == OutputsOf(composedHistory)
      ensures SecondAction().ValidInput(secondHistory, nextM)

    lemma CanReturn(firstHistory: seq<(I, M)>, secondHistory: seq<(M, O)>, composedHistory: seq<(I, O)>)
      requires FirstAction().ValidHistory(firstHistory)
      requires SecondAction().ValidHistory(secondHistory)
      ensures ComposedValidHistory(composedHistory)

    ghost predicate ComposedValidHistory(composedHistory: seq<(I, O)>): (result: bool)
      ensures composedHistory == [] ==> result
  }
}