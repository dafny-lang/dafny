module Std.BulkActions {

  import opened Actions
  import opened Consumers
  import opened Producers
  import opened Wrappers
  import opened BoundedInts

  datatype OptionResult<T, E> = Good(value: T) | Bad(error: E) | Done

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

  // @AssumeCrossModuleTermination
  // class SeqOfResultReader<T, E> extends Producer<Result<T, E>> {

  //   const r: Result<seq<T>, E>



  // }

  class Chunker<E> extends BulkAction<Option<Result<uint8, E>>, Producer<Option<Result<uint8, E>>>> {

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

    ghost predicate ValidHistory(history: seq<(Option<Result<uint8, E>>, Producer<Option<Result<uint8, E>>>)>)
      decreases Repr
    {
      true
    }

    ghost predicate ValidInput(history: seq<(Option<Result<uint8, E>>, Producer<Option<Result<uint8, E>>>)>, next: Option<Result<uint8, E>>)
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

    method Invoke(i: Option<Result<uint8, E>>) returns (o: Producer<Option<Result<uint8, E>>>)
      requires Requires(i)
      reads Reads(i)
      modifies Modifies(i)
      decreases Decreases(i), 0
      ensures Ensures(i, o)
    {
      var input := new SeqReader([i]);
      var output := new SeqWriter();
      var outputTotalProof := new SeqWriterTotalActionProof(output);
      BulkInvoke(input, output, outputTotalProof);
      o := output.values[0];
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

    // TODO: Consider dedicated three-state datatype instead of Option<Result<...>>
    // Result is all values produced, plus the terminal state: 
    // normal (Success(true)), EOI (Success(false)) or error (Failure(error))
    method CollectToSeqResult<T, E>(p: Producer<Option<Result<T, E>>>) returns (values: seq<T>, state: Result<bool, E>)
      requires p.Valid()
      reads p, p.Repr
      modifies p.Repr
      ensures p.ValidAndDisjoint()
      ensures p.Done()

    {
      // TODO: optimization - needs duplicate class to get around lack of compiled is
      // if p is MappedProducer<T, Option<Result<T, E>>> {
      //   var mp := p as MappedProducer;
      //   if mp.mapping is FunctionAction<T, Option<Result<T, E>>> {
      //     values := CollectToSeq(mp.original);
      //     state := Success(true);
      //     return;
      //   }
      // }

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
    method BulkInvoke(input: Producer<Option<Result<uint8, E>>>, 
                      output: IConsumer<Producer<Option<Result<uint8, E>>>>,
                      outputTotalProof: TotalActionProof<Producer<Option<Result<uint8, E>>>, ()>)
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
    {
      assert Valid();

      var inputSeq, state := CollectToSeqResult(input);
      chunkBuffer := chunkBuffer + inputSeq;
        
      while chunkSize as int <= |chunkBuffer|
        invariant fresh(Repr - old(Repr))
        invariant Valid()
        invariant fresh(input.Repr - old(input.Repr))
        invariant input.Valid()
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
    }
  }

}