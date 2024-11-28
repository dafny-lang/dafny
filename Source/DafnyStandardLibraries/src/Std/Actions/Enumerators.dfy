
module Std.Enumerators {

  import opened Actions
  import opened Aggregators
  import opened Wrappers
  import opened Math

  trait {:termination false} Enumerator<T> extends Action<(), Option<T>>, ProducesTerminatedProof<(), Option<T>> {
    ghost function Action(): Action<(), Option<T>> {
      this
    }
    ghost function FixedInput(): () {
      ()
    }
    ghost function StopFn(): Option<T> -> bool {
      StopWhenNone
    }
    predicate StopWhenNone(r: Option<T>) {
      r.None?
    }

    ghost predicate CanConsume(history: seq<((), Option<T>)>, next: ())
      requires CanProduce(history)
      decreases height
    {
      true
    }

    lemma CanConsumeAll(history: seq<((), Option<T>)>, next: ()) 
      requires Action().CanProduce(history) 
      ensures Action().CanConsume(history, next)
    {}

    lemma ProducesTerminated(history: seq<((), Option<T>)>)
      requires Action().CanProduce(history) 
      requires (forall i <- Inputs(history) :: i == FixedInput())
      ensures exists n: nat | n <= Limit() :: Terminated(Outputs(history), StopFn(), n)

    // For better readability
    method Next() returns (r: Option<T>) 
      requires Valid()
      reads Reads(())
      modifies Modifies(())
      ensures Ensures((), r)
      ensures r.Some? ==> Remaining() < old(Remaining())
    {
      CanConsumeAll(history, ());
      label before:
      r := Invoke(());
      if r.Some? {
        assert forall i <- old(Action().Consumed()) :: i == ();
        InvokeUntilTerminationMetricDecreased@before(r);
      }
    }
  }

  function Enumerated<T>(produced: seq<Option<T>>): seq<T> {
    if |produced| == 0 || produced[0].None? then
      []
    else
      [produced[0].value] + Enumerated(produced[1..])
  }

  method ForEach<T>(e: Enumerator<T>, a: Accumulator<T>) 
    requires e.Valid()
    requires a.Valid()
    requires e.Repr !! a.Repr
    modifies e.Repr, a.Repr
    // TODO: complete post-condition
    // ensures Enumerated(e.Produced()) == a.Consumed()
  {
    var t := e.Next();
    while t != None 
      invariant e.ValidAndDisjoint()
      invariant a.ValidAndDisjoint()
      invariant e.Repr !! a.Repr
      decreases e.Remaining()
    {
      a.CanConsumeAll(a.history, t.value);
      a.Accept(t.value);

      t := e.Next();
      if t == None {
        break;
      }
    }
  }

  class SeqEnumerator<T> extends Enumerator<T> {

    const elements: seq<T>
    var index: nat

    constructor(elements: seq<T>) 
      ensures Valid()
    {
      this.elements := elements;
      this.index := 0;

      Repr := {this};
      history := [];
    }

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      ensures Valid() ==> CanProduce(history)
      decreases height, 0
    {
      && this in Repr
      && CanProduce(history)
    }

    ghost predicate CanProduce(history: seq<((), Option<T>)>)
      decreases height
    {
      var index := |history|;
      var values := Min(index, |elements|);
      var nones := index - values;
      && (forall i <- Inputs(history) :: i == ())
      && Outputs(history) == Seq.Map(x => Some(x), elements[..values]) + Seq.Repeat(None, nones)
    }

    method Invoke(t: ()) returns (value: Option<T>) 
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
      ensures Ensures(t, value)
    {
      if |elements| <= index {
        value := None;
      } else {
        value := Some(elements[index]);
        index := index + 1;
      }
      Update((), value);
      // TODO: Doable but annoying
      assume CanProduce(history);
      assert Valid();
    }


    method RepeatUntil(t: (), stop: Option<T> -> bool, ghost eventuallyStopsProof: ProducesTerminatedProof<(), Option<T>>)
      requires Valid()
      requires eventuallyStopsProof.Action() == this
      requires eventuallyStopsProof.FixedInput() == t
      requires eventuallyStopsProof.StopFn() == stop
      requires forall i <- Consumed() :: i == t
      reads Reads(t)
      modifies Repr
      decreases Repr
      ensures Valid()
    {
      DefaultRepeatUntil(this, t, stop, eventuallyStopsProof);
    }

    ghost function Limit(): nat {
      |elements|
    }

    lemma ProducesTerminated(history: seq<((), Option<T>)>)
      requires Action().CanProduce(history) 
      requires (forall i <- Inputs(history) :: i == FixedInput())
      ensures exists n: nat | n <= Limit() :: Terminated(Outputs(history), StopFn(), n)
    {
      assert Terminated(Outputs(history), StopFn(), |elements|);
    }

  }

  trait {:termination false} Pipeline<U, T> extends Enumerator<T> {
    
    const upstream: Enumerator<U>
    const buffer: Collector<T>

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      ensures Valid() ==> CanProduce(history)
      decreases height, 0
    {
      && this in Repr
      && ValidComponent(upstream)
      && ValidComponent(buffer)
      && upstream.Repr !! buffer.Repr
      && CanProduce(history)
    }

    // TODO: needs refinement
    ghost predicate CanProduce(history: seq<((), Option<T>)>)
      decreases height
    {
      true
    }

    method {:verify false} Invoke(t: ()) returns (r: Option<T>) 
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
      ensures Ensures(t, r)
    {
      label start:
      while (|buffer.values| == 0) 
        invariant upstream.Repr !! buffer.Repr
        invariant fresh(Repr - old(Repr))
        invariant fresh(buffer.Repr - old(buffer.Repr))
        invariant fresh(upstream.Repr - old(upstream.Repr))
        invariant Valid()
        invariant buffer.ValidAndDisjoint()
        invariant upstream.ValidAndDisjoint()
        modifies Repr
        decreases upstream.Remaining()
      {
        var u := upstream.Next();
        Process(u, buffer);

        if u.None? {
          break;
        }

        Repr := {this} + upstream.Repr + buffer.Repr;
      }

      if 0 < |buffer.values| {
        var next := buffer.Pop();
        r := Some(next);
      } else {
        r := None;
      }
      Update(t, r);
    }

    method Process(u: Option<U>, a: Accumulator<T>)
      requires Valid()
      requires a.Valid()
      requires Repr !! a.Repr
      reads Repr, a.Repr
      modifies Repr, a.Repr
      ensures a.ValidAndDisjoint()
      // TODO: need a postcondition that a was invoked at least once etc

    method RepeatUntil(t: (), stop: Option<T> -> bool, ghost eventuallyStopsProof: ProducesTerminatedProof<(), Option<T>>)
      requires Valid()
      requires eventuallyStopsProof.Action() == this
      requires eventuallyStopsProof.FixedInput() == t
      requires eventuallyStopsProof.StopFn() == stop
      requires forall i <- Consumed() :: i == t
      reads Reads(t)
      modifies Repr
      decreases Repr
      ensures Valid()
    {
      DefaultRepeatUntil(this, t, stop, eventuallyStopsProof);
    }

    ghost function Limit(): nat {
      upstream.Limit()
    }

    lemma {:axiom} ProducesTerminated(history: seq<((), Option<T>)>)
      requires Action().CanProduce(history) 
      requires (forall i <- Inputs(history) :: i == FixedInput())
      ensures exists n: nat | n <= Limit() :: Terminated(Outputs(history), StopFn(), n)
    {
      // TODO
      assume {:axiom} false;
    }
  }

  class ExamplePipeline<T> extends Pipeline<T, T> {
    constructor(upstream: Enumerator<T>) 
      requires upstream.Valid()
      ensures Valid()
    {
      this.upstream := upstream;
      var buffer := new Collector<T>();

      Repr := {this} + upstream.Repr + buffer.Repr;
      history := [];
      this.buffer := buffer; 
      this.height := upstream.height + buffer.height + 1;
    }

    method Process(u: Option<T>, a: Accumulator<T>) 
      requires a.Valid()
      reads a.Repr
      modifies a.Repr
      ensures a.ValidAndDisjoint()
    {
      if u.Some? {
        a.Accept(u.value);
      }
    }
  }

  class PipelineProcessor<U, T> extends Action<Option<U>, ()> {

    const pipeline: Pipeline<U, T>
    const accumulator: Accumulator<T>

    constructor(pipeline: Pipeline<U, T>, accumulator: Accumulator<T>) {
      this.pipeline := pipeline;
      this.accumulator := accumulator;
    }

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      ensures Valid() ==> CanProduce(history)
      decreases height, 0
    {
      this in Repr 
    }

    ghost predicate CanConsume(history: seq<(Option<U>, ())>, next: Option<U>)
      requires CanProduce(history)
      decreases height
    {
      true
    }

    ghost predicate CanProduce(history: seq<(Option<U>, ())>)
      decreases height
    {
      true
    }

    method {:verify false} Invoke(u: Option<U>) returns (nothing: ()) {
      pipeline.Process(u, accumulator);
    }

    method RepeatUntil(t: Option<U>, stop: (()) -> bool, ghost eventuallyStopsProof: ProducesTerminatedProof<Option<U>, ()>)
      requires Valid()
      requires eventuallyStopsProof.Action() == this
      requires eventuallyStopsProof.FixedInput() == t
      requires eventuallyStopsProof.StopFn() == stop
      requires forall i <- Consumed() :: i == t
      reads Reads(t)
      modifies Repr
      decreases Repr
      ensures Valid()
    {
      DefaultRepeatUntil(this, t, stop, eventuallyStopsProof);
    }
  }

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
      reads Reads(t)
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
      assert Valid();
    }

    method RepeatUntil(t: (), stop: Option<T> -> bool, ghost eventuallyStopsProof: ProducesTerminatedProof<(), Option<T>>)
      requires Valid()
      requires eventuallyStopsProof.Action() == this
      requires eventuallyStopsProof.FixedInput() == t
      requires eventuallyStopsProof.StopFn() == stop
      requires forall i <- Consumed() :: i == t
      reads Reads(t)
      modifies Repr
      decreases Repr
      ensures Valid()
    {
      DefaultRepeatUntil(this, t, stop, eventuallyStopsProof);
    }
  }
}