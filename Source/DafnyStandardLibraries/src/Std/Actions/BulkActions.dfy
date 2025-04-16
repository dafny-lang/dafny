module Std.BulkActions {

  import opened Actions
  import opened Consumers
  import opened Producers
  import opened Wrappers
  import opened BoundedInts
  import opened Termination

  type StreamedValue<T, E> = Option<Result<T, E>>
  type StreamedByte<E> = Option<Result<uint8, E>>

  @AssumeCrossModuleTermination
  trait BulkAction<I, O> extends Action<I, O> {

    method BulkInvoke(input: Producer<I>, output: IConsumer<O>, outputTotalProof: TotalActionProof<O, ()>)
      requires Valid()
      requires input.Valid()
      requires output.Valid()
      requires outputTotalProof.Valid()
      requires outputTotalProof.Action() == output
      requires Repr !! input.Repr !! output.Repr !! outputTotalProof.Repr
      reads this, Repr, input, input.Repr, output, output.Repr, outputTotalProof, outputTotalProof.Repr
      modifies Repr, input.Repr, output.Repr, outputTotalProof.Repr
      ensures Valid()
      ensures input.Valid()
      ensures output.Valid()
  }
  
  /**
   * The equivalent of MappedProducer(ToOptionResult, original),
   * but a separate class so it's possible to optimize via "is" testing.
   */
  @AssumeCrossModuleTermination
  class BatchProducer<T, E> extends Producer<StreamedValue<T, E>> {

    const elements: seq<T>
    var index: nat

    constructor(elements: seq<T>)
      ensures Valid()
      ensures history == []
      ensures fresh(Repr)
      reads {}
      ensures this.elements == elements
      ensures index == 0
    {
      this.elements := elements;
      this.index := 0;

      Repr := {this};
      history := [];
    }

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases Repr, 0
    {
      && this in Repr
      && ValidHistory(history)
      && (Done() ==> index == |elements|)
      && index <= |elements|
      && Produced() == Seq.Map(ToOptionResult, elements[..index])
      && (index < |elements| ==> Seq.All(Outputs(), IsSome))
    }

    ghost predicate ValidOutputs(outputs: seq<Option<StreamedValue<T, E>>>)
      requires Seq.Partitioned(outputs, IsSome)
      decreases Repr
    {
      true
    }

    ghost function RemainingMetric(): TerminationMetric
      requires Valid()
      reads this, Repr
      decreases Repr, 3
    {
      TMNat(|elements| - index)
    }

    @IsolateAssertions
    method Invoke(t: ()) returns (value: Option<StreamedValue<T, E>>)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t), 0
      ensures Ensures(t, value)
      ensures RemainingDecreasedBy(value)
    {
      assert Requires(t);
      assert Valid();
      reveal TerminationMetric.Ordinal();

      if |elements| == index {
        value := None;

        OutputsPartitionedAfterOutputtingNone();
        ProduceNone();
      } else {
        value := Some(Some(Success(elements[index])));

        OutputsPartitionedAfterOutputtingSome(value.value);
        ProduceSome(value.value);
        index := index + 1;
      }

      assert Valid();
    }

    // TODO: Use this in an override of ForEachRemaining(seq consumer)
    @IsolateAssertions
    method Read() returns (s: seq<T>)
      requires Valid()
      reads this, Repr
      modifies Repr
      ensures ValidAndDisjoint()
      ensures Done()
    {
      // Avoid the slice if possible
      if index == 0 {
        s := elements;
      } else {
        s := elements[index..];
      }
      index := |elements|;

      var produced := Seq.Map(ToOptionResult, s);
      var outputs := OutputsForProduced(produced, |s| + 1);
      history := history + Seq.Zip(Seq.Repeat((), |s| + 1), outputs);
      assert Seq.Last(Outputs()) == None;
      assert Outputs() == old(Outputs()) + outputs;
      if |s| == 0 {
        assert Seq.AllNot(outputs, IsSome);
        Seq.PartitionedCompositionRight(old(Outputs()), outputs, IsSome);
      } else {
        assert Seq.All(old(Outputs()), IsSome);
        Seq.PartitionedCompositionLeft(old(Outputs()), outputs, IsSome);
      }
      ProducedComposition(old(Outputs()), outputs);
      
      assert Valid();
    }

  }

  function ToOptionResult<T, E>(t: T): Option<Result<T, E>> {
    Some(Success(t))
  }

  method ToOptionResultProducer<T, E>(values: seq<T>) returns (result: Producer<Option<Result<T, E>>>)
    reads {}
    ensures result.Valid()
    ensures fresh(result.Repr)
    ensures result.history == []
  {
    var chunkProducer := new SeqReader(values);
    var mapping := new FunctionAction(ToOptionResult);
    var mappingTotalProof := new TotalFunctionActionProof(mapping);
    result := new MappedProducer(chunkProducer, mapping, mappingTotalProof);
  }
  class Chunker<E> extends BulkAction<StreamedByte<E>, Producer<StreamedByte<E>>> {

    const chunkSize: uint64
    var chunkBuffer: BoundedInts.bytes

    constructor(chunkSize: uint64)
      requires 0 < chunkSize
      ensures Valid()
      ensures fresh(Repr)
      ensures history == []
    {
      this.chunkSize := chunkSize;
      chunkBuffer := [];
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
      && 0 < chunkSize
    }

    ghost predicate ValidHistory(history: seq<(StreamedByte<E>, Producer<StreamedByte<E>>)>)
      decreases Repr
    {
      true
    }

    ghost predicate ValidInput(history: seq<(StreamedByte<E>, Producer<StreamedByte<E>>)>, next: StreamedByte<E>)
      requires ValidHistory(history)
      decreases Repr
    {
      // TODO: Need constraint on when the None shows up,
      // OR drop the Option and use a different way of defining BulkInvoke for batches
      // so there is a separate "Done" hook after all of them
      // (or perhaps this is a different hook on MappedProducer?
      // MappedProducer could actually wrap an IProducer instead
      // and just prove that it eventually produces None?
      // Probably IMappedProducer or something instead)
      //
      // Tricky part of BulkInvoke is it's meant to be delivering a batch of values,
      // and None means end of batch, not end of all input.
      // Something like a Chunker needs an EOI to flush buffered values
      // (or produce an error!)
      // Options:
      //  * Mapped(input, action) + Something(action)
      //  * Mapped(LiftAndAddEOI(input), action) - Three-state data/error/done datatype?
      Seq.Partitioned(InputsOf(history) + [next], IsSome)
    }

    ghost function Decreases(i: Option<Result<uint8, E>>): ORDINAL
      requires Requires(i)
      reads Reads(i)
    {
      0
    }

    @ResourceLimit("0")
    method Invoke(i: StreamedByte<E>) returns (o: Producer<StreamedByte<E>>)
      requires Requires(i)
      reads this, Repr
      modifies Modifies(i)
      decreases Decreases(i), 0
      ensures Ensures(i, o)
    {
      assert Valid();
      var input := new SeqReader([i]);
      var output := new SeqWriter();
      var outputTotalProof := new SeqWriterTotalActionProof(output);
      BulkInvoke(input, output, outputTotalProof);
      assert input.Valid();
      assert |output.values| == 1;
      o := output.values[0];

      assert input.Produced() == [i];
      assert Inputs() == old(Inputs()) + [i];
      assert Outputs() == old(Outputs()) + [o];
    }

    

    // Result is all values produced, plus the terminal state:
    // normal (Success(true)), EOI (Success(false)) or error (Failure(error))
    // TODO: Consider dedicated three-state datatype instead of Option<Result<...>>
    // TODO: Make this an implementation of AcceptAll() for a kind of Consumer?
    method CollectToSeqResult<T, E>(p: Producer<Option<Result<T, E>>>) returns (values: seq<T>, state: Result<bool, E>)
      requires p.Valid()
      reads p, p.Repr
      modifies p.Repr
      ensures p.ValidAndDisjoint()
      ensures p.Done()
      // TODO: ensures relationship between p.Produced() and values/state
    {
      // Optimization
      if p is BatchProducer<T, E> {
        var bp := p as BatchProducer<T, E>;
        values := bp.Read();
        state := Success(true);
        return;
      }

      values := [];
      state := Success(true);
      while true 
        invariant fresh(p.Repr - old(p.Repr))
        invariant p.Valid()
        decreases p.Remaining()
      {
        var next := p.Next();
        if next.None? {
          assert Seq.Last(p.Outputs()) == None;
          assert p.Done();
          break;
        }

        match next.value {
          case Some(Success(t)) => values := values + [t];
          case Some(Failure(e)) => state := Failure(e);
          case None => state := Success(false);
        }
      }
      assert p.Done();
    }

    @ResourceLimit("0")
    method BulkInvoke(input: Producer<StreamedByte<E>>, 
                      output: IConsumer<Producer<StreamedByte<E>>>,
                      outputTotalProof: TotalActionProof<Producer<StreamedByte<E>>, ()>)
      requires Valid()
      requires input.Valid()
      requires output.Valid()
      requires outputTotalProof.Valid()
      requires outputTotalProof.Action() == output
      requires Repr !! input.Repr !! output.Repr !! outputTotalProof.Repr
      reads this, Repr, input, input.Repr, output, output.Repr, outputTotalProof, outputTotalProof.Repr
      modifies Repr, input.Repr, output.Repr, outputTotalProof.Repr
      ensures ValidAndDisjoint()
      ensures input.ValidAndDisjoint()
      ensures output.ValidAndDisjoint()
      ensures input.Done()
      ensures Inputs() == input.Produced()
      ensures Outputs() == output.Inputs()
    {
      assert Valid();

      var inputSeq, state := CollectToSeqResult(input);
      chunkBuffer := chunkBuffer + inputSeq;
        
      while chunkSize as int <= |chunkBuffer|
        invariant fresh(Repr - old(Repr))
        invariant Valid()
        invariant fresh(input.Repr - old(input.Repr))
        invariant input.Valid()
        invariant input.Done()
        invariant fresh(output.Repr - old(output.Repr))
        invariant output.Valid()
        invariant fresh(outputTotalProof.Repr - old(outputTotalProof.Repr))
        invariant outputTotalProof.Valid()
        invariant Repr !! input.Repr !! output.Repr !! outputTotalProof.Repr
        invariant history == old(history)
        decreases |chunkBuffer|
      {
        var nextChunk := chunkBuffer[..chunkSize];
        chunkBuffer := chunkBuffer[chunkSize..];

        var chunkProducer := ToOptionResultProducer(nextChunk);
        outputTotalProof.AnyInputIsValid(output.history, chunkProducer);
        output.Accept(chunkProducer);
      }

      match state {
      case Failure(error) =>
        var errorProducer := new SeqReader([Some(Failure(error))]);
        outputTotalProof.AnyInputIsValid(output.history, errorProducer);
        output.Accept(errorProducer);
      case Success(false) =>
        if 0 < |chunkBuffer| {
          // To make it more interesting, produce an error if outputChunks is non empty?
          var nextChunk := chunkBuffer;
          var chunkProducer := ToOptionResultProducer(nextChunk);
          outputTotalProof.AnyInputIsValid(output.history, chunkProducer);
          output.Accept(chunkProducer);
        }
      case Success(true) => {}
      }

      history := history + Seq.Zip(input.Produced(), output.Inputs());
    }
  }

}