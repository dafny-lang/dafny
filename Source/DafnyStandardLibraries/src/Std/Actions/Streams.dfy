/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Std.Streams {

  import opened Wrappers
  import opened Actions
  import opened Producers
  import opened BoundedInts
  import opened Termination
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
  //
  // TODO:
  //
  //  * ContentLength should be an Option<uint64>,
  //    but that currently ends up running into a conflict
  //    when trying to import Wrappers and Std.Wrappers at the same time.
  //  * This probably needs to support templating over error handling approaches somehow,
  //    since it can't be augmented by sub-traits.
  //
  @AssumeCrossModuleTermination
  trait ByteStream extends Producer<BoundedInts.bytes> {

    // The total length of all produced bytes
    function ContentLength(): (res: uint64)
      requires Valid()
      reads this, Repr

    ghost function ConcatenatedOutputsOf(history: seq<((), Option<bytes>)>): bytes
      requires Partitioned(OutputsOf(history), IsSome)
    {
      Flatten(ProducedOf(OutputsOf(history)))
    }

    // TODO: refine the specification to relate ContentLength()
    // to ConcatenatedOutputsOf(history)
  }

  trait RewindableByteStream extends ByteStream {

    ghost const data: BoundedInts.bytes

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases height, 0

    function ContentLength(): (res: uint64)
      requires Valid()
      reads this, Repr
      ensures res as int == |data|

    twostate predicate ValidOutput(history: seq<((), Option<bytes>)>, nextInput: (), new nextOutput: Option<bytes>)
      decreases height
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)])
    }
    ghost predicate ValidOutputs(outputs: seq<Option<bytes>>)
      requires Seq.Partitioned(outputs, IsSome)
      decreases height
    {
      Flatten(ProducedOf(outputs)) <= data
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
   * Wraps an Producer up as a non-rewindable DataStream.
   */
  class ProducerDataStream extends ByteStream {

    const wrapped: Producer<BoundedInts.bytes>
    const length: uint64

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases height, 0
    {
      && this in Repr
      && ValidComponent(wrapped)
      && ValidHistory(history)
      && remaining == wrapped.remaining
    }

    twostate predicate ValidOutput(history: seq<((), Option<bytes>)>, nextInput: (), new nextOutput: Option<bytes>)
      decreases height
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)])
    }
    ghost predicate ValidOutputs(outputs: seq<Option<bytes>>)
      decreases height
    {
      true
    }

    constructor(wrapped: Producer<BoundedInts.bytes>, length: uint64)
      requires wrapped.Valid()
      requires wrapped.history == []
      ensures Valid()
      ensures fresh(Repr - wrapped.Repr)
    {
      this.wrapped := wrapped;
      this.length := length;

      this.remaining := wrapped.remaining;
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
      decreases Decreases(t).Ordinal(), 0
      ensures Ensures(t, r)
      ensures if r.Some? then 
          old(remaining).DecreasesTo(remaining)
        else
          old(remaining) == remaining
    {
      assert Requires(t);

      assert Valid();
      r := wrapped.Next();
      UpdateHistory(t, r);
      
      assume {:axiom} Ensures(t, r);
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
      ensures Valid() ==> ValidHistory(history)
      decreases height, 0
    {
      && this in Repr
      && ValidHistory(history)
      && s == data
      && |s| <= UINT64_MAX as int
      && position as int <= |s|
      && ConcatenatedOutputsOf(history) == s[..position]
      && 0 < chunkSize
      && remaining == TMNat(|s| - position as int)
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

      this.remaining := TMNat(|s|);
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
      assume {:axiom} Valid();
    }

    method Invoke(t: ()) returns (r: Option<BoundedInts.bytes>)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal(), 0
      ensures Ensures(t, r)
      ensures if r.Some? then 
          old(remaining).DecreasesTo(remaining)
        else
          old(remaining) == remaining
    {
      assert Requires(t);

      if position == |s| as uint64 {
        r := None;
      } else {
        // Warning: unbounded integers
        var size := Math.Min(chunkSize as int, |s| - position as int) as uint64;
        var newPosition := position + size;
        r := Some(s[position..newPosition]);
        position := newPosition;
      }
      UpdateHistory(t, r);

      assume {:axiom} Ensures(t, r);
    }
  }
}