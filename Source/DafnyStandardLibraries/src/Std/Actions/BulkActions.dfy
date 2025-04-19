module Std.BulkActions {

  import opened Actions
  import opened Consumers
  import opened Producers
  import opened Wrappers
  import opened BoundedInts
  import opened Termination

  type StreamedValue<T, E> = Option<Result<T, E>>
  type StreamedByte<E> = StreamedValue<uint8, E>

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
      ensures ValidChange()
      ensures input.ValidChange()
      ensures output.ValidChange()
      ensures input.Done()
      ensures |input.NewProduced()| == |output.NewInputs()|
      ensures history == old(history) + Seq.Zip(input.NewProduced(), output.NewInputs())
  }
  
  /**
   * The equivalent of MappedProducer(ToOptionResult, original),
   * but a separate class so it's possible to optimize via "is" testing.
   */
  @AssumeCrossModuleTermination
  class BatchReader<T, E> extends Producer<StreamedValue<T, E>> {

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

    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()
    {}

    ghost predicate ValidOutputs(outputs: seq<Option<StreamedValue<T, E>>>)
      requires Seq.Partitioned(outputs, IsSome)
      decreases Repr
    {
      true
    }

    ghost function DecreasesMetric(): TerminationMetric
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
      ensures DecreasedBy(value)
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

    method ForEachRemaining(consumer: IConsumer<StreamedValue<T, E>>, ghost totalActionProof: TotalActionProof<StreamedValue<T, E>, ()>)
      requires Valid()
      requires consumer.Valid()
      requires Repr !! consumer.Repr !! totalActionProof.Repr
      requires totalActionProof.Valid()
      requires totalActionProof.Action() == consumer
      reads this, Repr, consumer, consumer.Repr, totalActionProof, totalActionProof.Repr
      modifies Repr, consumer.Repr
      ensures ValidChange()
      ensures consumer.ValidChange()
      ensures Done()
      ensures NewProduced() == consumer.NewInputs()
    {
      if consumer is BatchSeqWriter<T, E> {
        var writer := consumer as BatchSeqWriter<T, E>;
        var s := Read();
        
        writer.elements := writer.elements + s;
        var produced := Produced()[|old(Produced())|..];
        writer.history := writer.history + Seq.Zip(produced, Seq.Repeat((), |produced|));
        writer.events := writer.events + |s|;

        return;
      }

      DefaultForEachRemaining(this, consumer, totalActionProof);
    }

    // TODO: Use this in an override of ForEachRemaining(seq consumer)
    @IsolateAssertions
    method Read() returns (s: seq<T>)
      requires Valid()
      reads this, Repr
      modifies Repr
      ensures ValidAndDisjoint()
      ensures Done()
      ensures ValidChange()
      ensures |Produced()| == |old(Produced())| + |s|
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

  @AssumeCrossModuleTermination
  class BatchSeqWriter<T, E> extends IConsumer<StreamedValue<T, E>> {

    var elements: seq<T>
    var state: Result<bool, E>
    var events: nat

    constructor()
      ensures Valid()
      ensures history == []
      ensures fresh(Repr)
      reads {}
      ensures this.elements == []
      ensures state == Success(true)
    {
      this.elements := [];
      this.state := Success(true);
      this.events := 0;

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
      && events == |history|
    }

    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()
    {}

    ghost predicate ValidHistory(history: seq<(StreamedValue<T, E>, ())>)
      decreases Repr
    {
      true
    }
    ghost predicate ValidInput(history: seq<(StreamedValue<T, E>, ())>, next: StreamedValue<T, E>)
      requires ValidHistory(history)
      decreases Repr
    {
      true
    }

    ghost function Decreases(t: StreamedValue<T, E>): ORDINAL
      reads Reads(t)
    {
      0
    }

    @IsolateAssertions
    method Invoke(t: StreamedValue<T, E>) returns (r: ())
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t), 0
      ensures Ensures(t, r)
    {
      assert Requires(t);
      assert Valid();
      reveal TerminationMetric.Ordinal();

      match t {
        case Some(Success(t)) => elements := elements + [t];
        case Some(Failure(e)) => state := Failure(e);
        case None => state := Success(false);
      }
      r := ();
      events := events + 1;

      UpdateHistory(t, r);

      assert Valid();
    }
  }

  @AssumeCrossModuleTermination
  class BatchSeqWriterTotalProof<T, E> extends TotalActionProof<StreamedValue<T, E>, ()> {
    ghost const action: BatchSeqWriter<T, E>

    ghost constructor (action: BatchSeqWriter<T, E>)
      reads {}
      ensures Valid()
      ensures fresh(Repr)
      ensures Action() == action
    {
      this.action := action;
      this.Repr := {this};
    }

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr, 0
    {
      && this in Repr
    }

    twostate predicate ValidChange()
      reads this, Repr
      ensures ValidChange() ==> old(Valid()) && Valid()
      decreases Repr, 0
    {
      old(Valid()) && Valid()
    }
   
    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()
    {}

    ghost function Action(): Action<StreamedValue<T, E>, ()> {
      action
    }

    lemma AnyInputIsValid(history: seq<(StreamedValue<T, E>, ())>, next: StreamedValue<T, E>)
      requires Valid()
      requires Action().ValidHistory(history)
      ensures Action().ValidInput(history, next)
    {}
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
  class Chunker<E> extends BulkAction<StreamedByte<E>, seq<StreamedByte<E>>> {

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

    twostate predicate ValidChange()
      reads this, Repr
      ensures ValidChange() ==> old(Valid()) && Valid()
      ensures ValidChange() ==> fresh(Repr - old(Repr))
      ensures ValidChange() ==> old(history) <= history
    {
      && fresh(Repr - old(Repr))
      && old(Valid())
      && Valid()
      && old(history) <= history
    }
   
    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()
    {}

    ghost predicate ValidHistory(history: seq<(StreamedByte<E>, seq<StreamedByte<E>>)>)
      decreases Repr
    {
      true
    }

    ghost predicate ValidInput(history: seq<(StreamedByte<E>, seq<StreamedByte<E>>)>, next: StreamedByte<E>)
      requires ValidHistory(history)
      decreases Repr
    {
      true
    }

    ghost function Decreases(i: Option<Result<uint8, E>>): ORDINAL
      requires Requires(i)
      reads Reads(i)
    {
      0
    }

    @IsolateAssertions
    method Invoke(i: StreamedByte<E>) returns (o: seq<StreamedByte<E>>)
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
      label before:
      BulkInvoke(input, output, outputTotalProof);
      assert |output.values| == 1;
      o := output.values[0];
      assert Seq.Last(output.Inputs()) == o;
      assert Seq.Last(Inputs()) == i;
    }

    @ResourceLimit("0")
    @IsolateAssertions
    method {:only} BulkInvoke(input: Producer<StreamedByte<E>>, 
                      output: IConsumer<seq<StreamedByte<E>>>,
                      outputTotalProof: TotalActionProof<seq<StreamedByte<E>>, ()>)
      requires Valid()
      requires input.Valid()
      requires output.Valid()
      requires outputTotalProof.Valid()
      requires outputTotalProof.Action() == output
      requires Repr !! input.Repr !! output.Repr !! outputTotalProof.Repr
      reads this, Repr, input, input.Repr, output, output.Repr, outputTotalProof, outputTotalProof.Repr
      modifies Repr, input.Repr, output.Repr, outputTotalProof.Repr
      ensures ValidChange()
      ensures input.ValidChange()
      ensures output.ValidChange()
      ensures input.Done()
      ensures input.NewProduced() == NewInputs()
      ensures |input.NewProduced()| == |output.NewInputs()|
      ensures output.NewInputs() == NewOutputs()
    {
      assert Valid();

      var batchWriter := new BatchSeqWriter();
      var batchWriterTotalProof := new BatchSeqWriterTotalProof(batchWriter);
      label before:
      input.ForEachRemaining(batchWriter, batchWriterTotalProof);
      assert input.ValidChange@before();
      assert input.ValidChange();

      if batchWriter.events == 0 {
        // No-op
        assert input.ValidChange();
        assert |batchWriter.Inputs()| == 0;
        assert input.NewProduced() == batchWriter.Inputs();
        assert |input.NewProduced()| == 0;
        output.ValidImpliesValidChange();
        return;
      }

      chunkBuffer := chunkBuffer + batchWriter.elements;
        
      // TODO: Move loop to its own method to isolate the specification better
      var chunks: seq<uint8> := [];
      while chunkSize as int <= |chunkBuffer|
        invariant fresh(Repr - old(Repr))
        invariant Valid()
        invariant fresh(input.Repr - old(input.Repr))
        invariant input.ValidChange()
        invariant input.Done()
        invariant fresh(output.Repr - old(output.Repr))
        invariant output.ValidChange()
        invariant fresh(outputTotalProof.Repr - old(outputTotalProof.Repr))
        invariant outputTotalProof.Valid()
        invariant Repr !! input.Repr !! output.Repr !! outputTotalProof.Repr
        invariant history == old(history)
        invariant 0 < batchWriter.events
        decreases |chunkBuffer|
      {
        chunks := chunks + Seq.Reverse(chunkBuffer[..chunkSize]);
        chunkBuffer := chunkBuffer[chunkSize..];
      }

      var outputProducer: Producer<StreamedByte<E>>;
      match batchWriter.state {
      case Failure(error) =>
        outputProducer := new SeqReader([Some(Failure(error))]);
      case Success(more) =>
        if !more && 0 < |chunkBuffer| {
          // To make it more interesting, produce an error if outputChunks is non empty?
          chunks := chunks + Seq.Reverse(chunkBuffer);
        }
        outputProducer := new BatchReader(chunks);
      }

      // TODO: Find the right way to keep this as a batch,
      // this is just to get it resolving again
      var data := CollectToSeq(outputProducer);
      var dataReader := new SeqReader([data]);
      var padding := new RepeatProducer(batchWriter.events - 1, []);
      var concatenated: Producer<seq<StreamedByte<E>>> := new ConcatenatedProducer(padding, dataReader);
      concatenated.ForEachRemaining(output, outputTotalProof);

      // TODO:
      assert {:only} |input.NewProduced()| == |output.NewInputs()|;
      history := history + Seq.Zip(input.NewProduced(), output.NewInputs());
    }
  }

}