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

  // TODO: Move to readme, and/or convert to dafny docs
  //
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
  // the ValidInput and ValidHistory predicates,
  // which the action's specification of behavior are drawn from,
  // specifically avoid reading the current state of the action.
  // That is so extrinsic properties of an action do NOT depend on their current state.
  // This is key to ensure that you can prove properties of a given action that
  // will continue to hold as the Dafny heap changes.
  // This approach works because Dafny understands that for a given object,
  // the implementation of ValidInput/ValidHistory cannot change over time.
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
  // for I and O, under the assumption that
  // future Dafny backends will be able to easily optimize
  // away the overhead of passing around a pointless () value
  // or wrapping up multiple values into a tuple.
  //
  // === Errors ===
  //
  // Because the Action trait is so general,
  // there are many error producing and handling patterns that
  // can be expressed, even within the same type signature:
  //
  // 1. An Action<I, Option<O>> can produce None to indicate there is no value,
  //    but the action could still be called again. Similarly a Result<O, E>
  //    output could indicate a failure that is only related to that invocation.
  // 2. An Action<I, Option<O>> could also produce None to indicate the action
  //    is "exhausted" and cannot produce any more values.
  //    This is the basis for the IProducer specialization.
  //    Similarly a Result<O, E> could indicate the action is broken
  //    for abnormal reasons and can't be called again.
  // 3. An Action<I, Option<Result<O, E>> can indicate both cases independently:
  //    a Some(Success(O)) provides another value, 
  //    a None indicate no more values,
  //    and a Some(Failure(E)) indicates an error.
  //    The error could be fatal or recoverable depending on the protocol.
  // 4. For even better readability, it is often better to declare a more specialized datatype,
  //    such as
  //    
  //    datatype DataStreamEvent = 
  //      | NoData 
  //      | Done 
  //      | Data(values: bytes)
  //      | BadData(error: string)
  //      | FatalError(error: string)
  //
  //    along with rules for what sequences of these values are valid
  //    (e.g. once Done appears no other constructors can appear,
  //    and perhaps if you get a FatalError the ValidInput constraints
  //    don't even let you invoke the action again)
  //
  // The key point in distinguishing these semantics 
  // is how ValidInput and ValidHistory are constrained, 
  // defining the protocol for using the action across time,
  // depending on what inputs and outputs occur.
  // All of the above cases are useful for precisely modeling behavior over time,
  // and so this library provides explicit specializations for some common patterns
  // but allows for basically any well-founded approach.
  //
  // === Specializations ===
  //
  // In practice, many actions fit into a more specific version of this concept.
  // See the other sibling files for some useful specializations:
  //
  // TODO: ASCII Table?
  //
  //     - IProducer<T> = Action<(), T>         (consumes nothing, may produce infinite values)
  //     - Producer<T>  = Action<(), Option<T>> (consumes nothing, must prduce finite values)
  //     - IConsumer<T> = Action<T, ()>         (produces nothing, may consume infinite values)
  //     - Consumer<T>  = Action<T, boolean>    (produces nothing, may be eventually exhausted and output false)
  //
  // These concepts are duals to each other (IProducer/IConsumer, and Producer/Consumer).
  // The generic signatures of Producer and Consumer are not exact mirror-images
  // because in both cases they must produce an additional piece of boolean information
  // about whether they are "exhausted".
  //
  // In practice, the most common traits will usually be Producer and IConsumer. 
  // That is, most data sources in real programs tend to produce finite elements,
  // and it's usually impractical and/or unnecessary to specify how many statically,
  // but most data sinks tend to have no constraints.
  //
  @AssumeCrossModuleTermination
  trait Action<I, O> extends GenericAction<I, O>, Validatable {

    ghost var history: seq<(I, O)>

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases height, 0

    ghost predicate ValidHistory(history: seq<(I, O)>)
      decreases height

    ghost predicate ValidInput(history: seq<(I, O)>, next: I)
      requires ValidHistory(history)
      decreases height

    twostate predicate ValidOutput(history: seq<(I, O)>, nextInput: I, new nextOutput: O)
      decreases height
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])

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
    ghost function Decreases(i: I): TerminationMetric
      reads Reads(i)
    {
      NatTerminationMetric(height)
    }
    twostate predicate Ensures(i: I, new o: O)
      reads Reads(i)
    {
      && ValidAndDisjoint()
      && ValidOutput(old(history), i, o)
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

  // Common action invariants

  function InputsOf<I, O>(history: seq<(I, O)>): seq<I> {
    Seq.Map((e: (I, O)) => e.0, history)
  }

  function OutputsOf<I, O>(history: seq<(I, O)>): seq<O> {
    Seq.Map((e: (I, O)) => e.1, history)
  }

  // A proof that a given action accepts any I value as input,
  // independent of history.
  @AssumeCrossModuleTermination
  trait TotalActionProof<I, O> extends Validatable {
    ghost function Action(): Action<I, O>

    lemma AnyInputIsValid(history: seq<(I, O)>, next: I)
      requires Valid()
      requires Action().ValidHistory(history)
      ensures Action().ValidInput(history, next)
  }

  ghost predicate OnlyOutputs<I, O>(i: Action<I, O>, history: seq<(I, O)>, c: O) {
    i.ValidHistory(history) <==> forall e <- history :: e.1 == c
  }

  ghost predicate Terminated<I>(s: seq<I>, stop: I -> bool, n: nat) {
    forall i | 0 <= i < |s| :: n <= i <==> stop(s[i])
  }

  lemma TerminatedDistributes<I>(left: seq<I>, right: seq<I>, stop: I -> bool, n: nat)
    requires Terminated(left, stop, |left|)
    requires Terminated(right, stop, n)
    ensures Terminated(left + right, stop, |left| + n)
  {}

  lemma TerminatedUndistributes<I>(left: seq<I>, right: seq<I>, stop: I -> bool, n: nat)
    requires Terminated(left + right, stop, n)
    ensures Terminated(left, stop, n)
    ensures Terminated(right, stop, Max(0, n - |left|))
  {
    assert forall i | 0 <= i < |left| :: left[i] == (left + right)[i];
    assert forall i | 0 <= i < |right| :: right[i] == (left + right)[i + |left|];
  }

  trait OutputsTerminatedProof<I, O> extends TotalActionProof<I, O> {

    ghost function FixedInput(): I
    ghost function StopFn(): O -> bool
    ghost function Limit(): nat

    // TODO: Return n instead of exists n
    lemma OutputsTerminated(history: seq<(I, O)>)
      requires Action().ValidHistory(history)
      requires forall i <- InputsOf(history) :: i == FixedInput()
      ensures exists n: nat | n <= Limit() :: Terminated(OutputsOf(history), StopFn(), n)

    // Termination metric
    ghost function Remaining(): nat
      requires Action().Valid()
      requires forall i <- Action().Inputs() :: i == FixedInput()
      reads Action().Repr
    {
      OutputsTerminated(Action().history);
      var n: nat :| n <= Limit() && Terminated(Action().Outputs(), StopFn(), n);
      TerminatedDefinesNonTerminalCount(Action().Outputs(), StopFn(), n);
      Limit() - NonTerminalCount(Action().Outputs(), StopFn())
    }

    twostate lemma InvokeUntilTerminationMetricDecreased(new nextProduced: O)
      requires old(Action().Valid())
      requires Action().Valid()
      requires forall i <- old(Action().Inputs()) :: i == FixedInput()
      requires Action().Inputs() == old(Action().Inputs()) + [FixedInput()]
      requires Action().Outputs() == old(Action().Outputs()) + [nextProduced]
      requires !StopFn()(nextProduced)
      ensures Remaining() < old(Remaining())
    {
      var before := old(Action().Outputs());
      var after := Action().Outputs();
      OutputsTerminated(old(Action().history));
      var n: nat :| n <= Limit() && Terminated(before, StopFn(), n);
      OutputsTerminated(Action().history);
      var m: nat :| m <= Limit() && Terminated(after, StopFn(), m);
      if n < |before| {
        assert false by {
          assert StopFn()(before[|before| - 1]);
          assert !StopFn()(Action().Outputs()[|Action().Outputs()| - 1]);
          assert |Action().Outputs()| <= m;
          assert !StopFn()(Action().Outputs()[|before| - 1]);
        }
      } else {
        TerminatedDefinesNonTerminalCount(before, StopFn(), n);
        assert NonTerminalCount(before, StopFn()) <= n;
        TerminatedDistributes(before, [nextProduced], StopFn(), 1);
        assert Terminated(after, StopFn(), |after|);
        TerminatedDefinesNonTerminalCount(after, StopFn(), |after|);
      }
    }
  }

  function NonTerminalCount<I>(produced: seq<I>, stop: I -> bool): nat {
    if |produced| == 0 || stop(produced[0]) then
      0
    else
      1 + NonTerminalCount(produced[1..], stop)
  }

  lemma TerminatedDefinesNonTerminalCount<I>(s: seq<I>, stop: I -> bool, n: nat)
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

  class FunctionAction<I, O> extends Action<I, O> {

    const f: I --> O

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==>
                && ValidHistory(history)
      decreases height, 0
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
      height := 0;
    }

    ghost predicate ValidHistory(history: seq<(I, O)>)
      decreases height
    {
      forall e <- history :: f.requires(e.0) && e.1 == f(e.0)
    }
    ghost predicate ValidInput(history: seq<(I, O)>, next: I)
      requires ValidHistory(history)
      decreases height
    {
      f.requires(next)
    }
    twostate predicate ValidOutput(history: seq<(I, O)>, nextInput: I, new nextOutput: O)
      decreases height
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)])
    }

    method {:rlimit 0} Invoke(i: I) returns (o: O)
      requires Requires(i)
      reads Reads(i)
      modifies Modifies(i)
      decreases Decreases(i).Ordinal()
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
      height := 0;
    }

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases height, 0
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
      height := first.height + second.height + 1;
    }

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases height, 0
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
      decreases height
    {
      compositionProof.ComposedValidHistory(history)
    }
    ghost predicate ValidInput(history: seq<(I, O)>, next: I)
      decreases height
    {
      compositionProof.ComposedValidInput(history, next)
    }
    twostate predicate ValidOutput(history: seq<(I, O)>, nextInput: I, new nextOutput: O)
      decreases height
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)])
    }

    @IsolateAssertions
    @ResourceLimit("0")
    method Invoke(i: I) returns (o: O)
      requires Requires(i)
      reads Reads(i)
      modifies Modifies(i)
      decreases Decreases(i).Ordinal()
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
      height := first.height + second.height + 1;

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

  // Minimal proof for composing actions with no preconditions,
  // but also creates a composition with no constraints on the outputs.
  class TotalActionCompositionProof<I, M, O> extends ActionCompositionProof<I, M, O> {

    const firstConsumeAllProof: TotalActionProof<I, M>
    const secondConsumeAllProof: TotalActionProof<M, O>

    ghost constructor(firstConsumeAllProof: TotalActionProof<I, M>,
                secondConsumeAllProof: TotalActionProof<M, O>)
    {
      this.firstConsumeAllProof := firstConsumeAllProof;
      this.secondConsumeAllProof := secondConsumeAllProof;
    }

    ghost function FirstAction(): Action<I, M> {
      firstConsumeAllProof.Action()
    }

    ghost function SecondAction(): Action<M, O> {
      secondConsumeAllProof.Action()
    }

    ghost predicate ComposedValidInput(composedHistory: seq<(I, O)>, next: I) {
      true
    }

    lemma CanInvokeFirst(firstHistory: seq<(I, M)>, composedHistory: seq<(I, O)>, next: I)
      requires FirstAction().ValidHistory(firstHistory)
      requires ComposedValidInput(composedHistory, next)
      requires InputsOf(firstHistory) == InputsOf(composedHistory)
      ensures FirstAction().ValidInput(firstHistory, next)
    {
      assert firstConsumeAllProof.Action().ValidHistory(firstHistory);
      assume {:axiom} firstConsumeAllProof.Valid();
      firstConsumeAllProof.AnyInputIsValid(firstHistory, next);
    }

    lemma CanInvokeSecond(secondHistory: seq<(M, O)>, composedHistory: seq<(I, O)>, nextT: I, nextM: M)
      requires SecondAction().ValidHistory(secondHistory)
      requires OutputsOf(secondHistory) == OutputsOf(composedHistory)
      ensures SecondAction().ValidInput(secondHistory, nextM)
    {
      assert secondConsumeAllProof.Action().ValidHistory(secondHistory);
      assume {:axiom} secondConsumeAllProof.Valid();
      secondConsumeAllProof.AnyInputIsValid(secondHistory, nextM);
    }

    lemma CanReturn(firstHistory: seq<(I, M)>, secondHistory: seq<(M, O)>, composedHistory: seq<(I, O)>)
      requires FirstAction().ValidHistory(firstHistory)
      requires SecondAction().ValidHistory(secondHistory)
      ensures ComposedValidHistory(composedHistory)
    {}

    ghost predicate ComposedValidHistory(composedHistory: seq<(I, O)>): (result: bool)
      ensures composedHistory == [] ==> result
    {
      true
    }
  }

  // Other primitives/examples todo:
  //  * Promise-like single-use Action<I, ()> to capture a value for reading later
  //  * datatype/codatatype-based enumerations
  //  * Expressing that an Action "Eventually produces something" (look at how VMC models this for randomness)
  //    * Build on that to make CrossProduct(enumerable1, enumerable2)
  //  * Example of enumerating all possible values of a type (for test generation)
  //    * Needs to handle infinite types too, hence needs the "eventually produces something" concept
  //  * Document: useful pattern to add an Action<Command, Result> facade
  //        to a set of methods that participate in a protocol.
  //        Then you have a history that ties the behavior
  //        of the methods together,
  //        supporting constraints on the order of calls etc.
}