/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

// TODO: Relocate under Actions/ instead, I don't think Streams has to be a separate library?
module Std.Streams {

  import opened Wrappers
  import opened Actions
  import opened Enumerators
  import opened BoundedInts
  import opened Collections.Seq

  //
  // A binary data stream.
  //
  // Allows for streams that can only be read once,
  // but see RewindableDataStream for a more specific trait
  // that requires the ability to replay the enumeration,
  // or seek to an arbitrary position (although this may take linear time).
  // That requirement is not in this trait
  // because there are lots of ways to implement a stream
  // where having to replay forces buffering all previous values in memory,
  // which often defeats the purpose of streaming in the first place.
  // In particular, boto3 currently (quite implicitly)
  // requires file-like streams with the ability to seek,
  // but we don't want to force the same requirements on all streams.
  //
  // Known limitations:
  //
  //  * ContentLength should be an Option<uint64>,
  //    but that currently ends up running into a conflict
  //    when trying to import Wrappers and Std.Wrappers at the same time.
  //
  @AssumeCrossModuleTermination
  trait ByteStream extends Enumerator<BoundedInts.bytes> {

    function ContentLength(): (res: uint64)
      requires Valid()
      reads this, Repr

    ghost function ConcatenatedOutputs(history: seq<((), Option<bytes>)>): bytes {
      Flatten(Enumerated(Outputs(history)))
    }

    // TODO: refine the specification to relate ContentLength()
    // to ConcatenatedOutputs(history)
  }

  trait RewindableByteStream extends ByteStream {

    ghost const data: BoundedInts.bytes

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> CanProduce(history)
      decreases height, 0

    function ContentLength(): (res: uint64)
      requires Valid()
      reads this, Repr
      ensures res as int == |data|

    ghost predicate CanProduce(history: seq<((), Option<bytes>)>)
      decreases height
    {
      && (forall o <- Enumerated(Outputs(history)) :: 0 < |o|)
      && ConcatenatedOutputs(history) <= data
    }

    lemma {:axiom} ProducesTerminated(history: seq<((), Option<bytes>)>)
      requires Action().CanProduce(history)
      requires (forall i <- Inputs(history) :: i == FixedInput())
      ensures exists n: nat | n <= Limit() :: Terminated(Outputs(history), StopFn(), n)
    // {
    //   assert Terminated(Outputs(history), StopFn(), |Enumerated(Outputs(history))|);
    // }

    method RepeatUntil(t: (), stop: Option<bytes> -> bool, ghost eventuallyStopsProof: ProducesTerminatedProof<(), Option<bytes>>)
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

    function Position(): (res: uint64)
      requires Valid()
      reads this, Repr
      decreases height, 2
      ensures res as int <= |data|

    method Seek(newPosition: uint64)
      requires Valid()
      requires newPosition as int <= |data|
      modifies Repr
      ensures Valid()
      ensures Position() == newPosition
  }

  /*
   * Wraps an Enumerator up as a non-rewindable DataStream.
   */
  class EnumeratorDataStream extends ByteStream {

    const wrapped: Enumerator<BoundedInts.bytes>
    const length: uint64

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> CanProduce(history)
      decreases height, 0
    {
      && this in Repr
      && ValidComponent(wrapped)
      && CanProduce(history)
    }

    ghost predicate CanProduce(history: seq<((), Option<bytes>)>)
      decreases height
    {
      && (forall o <- Enumerated(Outputs(history)) :: 0 < |o|)
    }

    lemma {:axiom} ProducesTerminated(history: seq<((), Option<BoundedInts.bytes>)>)
      requires Action().CanProduce(history)
      requires (forall i <- Inputs(history) :: i == FixedInput())
      ensures exists n: nat | n <= Limit() :: Terminated(Outputs(history), StopFn(), n)

    ghost function Limit(): nat {
      wrapped.Limit()
    }

    constructor(wrapped: Enumerator<BoundedInts.bytes>, length: uint64)
      requires wrapped.Valid()
      requires wrapped.history == []
      ensures Valid()
      ensures fresh(Repr - wrapped.Repr)
    {
      this.wrapped := wrapped;
      this.length := length;

      this.history := [];
      this.Repr := {this} + wrapped.Repr;
      this.height := wrapped.height + 1;
    }

    function ContentLength(): (res: uint64)
      requires Valid()
      reads this, Repr
    {
      length
    }

    predicate Rewindable()
      decreases height, 1
    {
      false
    }

    method Invoke(t: ()) returns (r: Option<BoundedInts.bytes>)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
      ensures Ensures(t, r)
    {
      assert Requires(t);

      assert Valid();
      r := wrapped.Next();
      Update(t, r);

      // TODO: Work to do
      assume {:axiom} Ensures(t, r);
    }

    method RepeatUntil(t: (), stop: Option<bytes> -> bool, ghost eventuallyStopsProof: ProducesTerminatedProof<(), Option<bytes>>)
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

  /*
   * Rewindable stream of a sequence with a configured chunk size.
   */
  class SeqByteStream extends RewindableByteStream {

    const s: BoundedInts.bytes
    const chunkSize: uint64
    var position: uint64

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> CanProduce(history)
      decreases height, 0
    {
      && this in Repr
      && CanProduce(history)
      && s == data
      && |s| <= UINT64_MAX as int
      && position as int <= |s|
      && ConcatenatedOutputs(history) == s[..position]
      && 0 < chunkSize
    }

    lemma {:axiom} ProducesTerminated(history: seq<((), Option<BoundedInts.bytes>)>)
      requires Action().CanProduce(history)
      requires (forall i <- Inputs(history) :: i == FixedInput())
      ensures exists n: nat | n <= Limit() :: Terminated(Outputs(history), StopFn(), n)

    ghost function Limit(): nat {
      |s|
    }

    constructor(s: BoundedInts.bytes, chunkSize: uint64)
      requires |s| <= UINT64_MAX as int
      requires 0 < chunkSize
      ensures Valid()
    {
      this.data := s;
      this.s := s;
      this.position := 0;
      this.chunkSize := chunkSize;

      this.history := [];
      this.Repr := {this};
      this.height := 1;
    }

    function ContentLength(): (res: uint64)
      requires Valid()
      reads this, Repr
      ensures res as int == |data|
    {
      |s| as uint64
    }

    predicate Rewindable()
      decreases height, 1
    {
      true
    }

    function Position(): (res: uint64)
      requires Valid()
      requires Rewindable()
      reads this, Repr
      decreases height, 2
      ensures res as int <= |data|
    {
      position
    }

    method Seek(newPosition: uint64)
      requires Valid()
      requires Rewindable()
      requires newPosition as int <= |data|
      modifies Repr
      ensures Valid()
      ensures Position() == newPosition
    {
      position := newPosition;
      history := [((), Some(s[..position]))];
      // TODO: work to do
      assume {:axiom} Valid();
    }

    method Invoke(t: ()) returns (r: Option<BoundedInts.bytes>)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
      ensures Ensures(t, r)
    {
      assert Requires(t);

      assert Valid();
      if position == |s| as uint64 {
        r := None;
      } else {
        // Warning: unbounded integers
        var size := Math.Min(chunkSize as int, |s| - position as int) as uint64;
        var newPosition := position + size;
        r := Some(s[position..newPosition]);
        position := newPosition;
      }
      Update(t, r);

      // TODO: Work to do
      assume {:axiom} Ensures(t, r);
    }
  }
}