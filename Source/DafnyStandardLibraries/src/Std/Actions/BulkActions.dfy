module Std.BulkActions {

  import opened Actions
  import opened Consumers
  import opened Producers
  import opened Wrappers
  import opened BoundedInts

  @AssumeCrossModuleTermination
  trait BulkAction<I, O> extends Action<I, O> {

    method BulkInvoke(input: Producer<I>, output: IConsumer<O>)
      requires input.Valid()
      requires output.Valid()
    
  }

  // @AssumeCrossModuleTermination
  // class SeqOfResultReader<T, E> extends Producer<Result<T, E>> {

  //   const r: Result<seq<T>, E>



  // }

  class Chunker<E> extends BulkAction<Option<Result<uint8, E>>, Option<Producer<Result<uint8, E>>>> {

    const chunkSize: uint64
    var chunkBuffer: BoundedInts.bytes

    constructor(chunkSize: uint64)
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
      this in Repr
    }

    ghost predicate ValidHistory(history: seq<(Option<Result<uint8, E>>, Option<Producer<Result<uint8, E>>>)>)
      decreases Repr
    {
      true
    }

    ghost predicate ValidInput(history: seq<(Option<Result<uint8, E>>, Option<Producer<Result<uint8, E>>>)>, next: Option<Result<uint8, E>>)
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
      true
    }

    ghost function Decreases(i: Option<Result<uint8, E>>): ORDINAL
      requires Requires(i)
      reads Reads(i)
    {
      0
    }

    method Invoke(i: Option<Result<uint8, E>>) returns (o: Option<Producer<Result<uint8, E>>>)
      requires Requires(i)
      reads Reads(i)
      modifies Modifies(i)
      decreases Decreases(i), 0
      ensures Ensures(i, o)
    {
      var input := new SeqReader([i]);
      var output := new SeqWriter();
      BulkInvoke(input, output);
      o := output.values[0];
    }

    

    method CollectToSeqResult<T, E>(p: Producer<Result<T, E>>) returns (r: Result<seq<T>, E>)
      requires p.Valid()
      ensures p.Valid()
      ensures p.Done()

    {
      if p is MappedProducer {
        // TODO: optimization
      }

      var s := CollectToSeq(p);
      var optIndex := Seq.IndexByOption(s, (x: Result<T, E>) => x.Failure?);
      match optIndex {
        case Some(index) =>
          r := Failure(s[index].error);
        case None =>
          r := Success(Seq.Map((x: Result<T, E>) => x.value, s));
      }
    }

    method BulkInvoke(input: Producer<Option<Result<uint8, E>>>, output: IConsumer<Option<Producer<Result<uint8, E>>>>)
      requires input.Valid()
      requires output.Valid()
    {
      assert Valid();
      var outputChunks := [];

      var inputSeq := CollectToSeqResult(input);

      if input.Some? {
        if input.value.Failure? {
          outputChunks := outputChunks + [input.value];
        } else {

          chunkBuffer := chunkBuffer + input.value.value;
          
          while chunkSize as int <= |chunkBuffer|
            invariant ValidAndDisjoint()
            invariant history == old(history)
          {
            outputChunks := outputChunks + [Success(chunkBuffer[..chunkSize])];
            chunkBuffer := chunkBuffer[chunkSize..];
          }
        }
      } else {
        if 0 < |chunkBuffer| {
          outputChunks := outputChunks + [Success(chunkBuffer)];
        } else {
          r := None;
          UpdateHistory(input, r);
          return;
        }
      }
      var output := new SeqReader(outputChunks);
      r := Some(output);
      UpdateHistory(input, r);
    }
  }

}