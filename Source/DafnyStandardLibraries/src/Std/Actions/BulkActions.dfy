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
      ensures ValidAndDisjoint()
      ensures input.ValidAndDisjoint()
      ensures output.ValidAndDisjoint()
      ensures input.Done()
      ensures |input.Produced()| == |output.Inputs()|
      ensures history == old(history) + Seq.Zip(input.Produced(), output.Inputs())
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

    method ForEachRemaining(consumer: IConsumer<StreamedValue<T, E>>, ghost totalActionProof: TotalActionProof<StreamedValue<T, E>, ()>)
      requires Valid()
      requires consumer.Valid()
      requires Repr !! consumer.Repr !! totalActionProof.Repr
      requires totalActionProof.Valid()
      requires totalActionProof.Action() == consumer
      reads this, Repr, consumer, consumer.Repr, totalActionProof, totalActionProof.Repr
      modifies Repr, consumer.Repr
      ensures ValidAndDisjoint()
      ensures consumer.ValidAndDisjoint()
      ensures Done()
      ensures old(Produced()) <= Produced()
      ensures old(consumer.Inputs()) <= consumer.Inputs()
      ensures Produced()[|old(Produced())|..] == consumer.Inputs()[|old(consumer.Inputs())|..]
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
      ensures old(Produced()) <= Produced()
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
    var events: int

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
      true
    }

    ghost function Decreases(i: Option<Result<uint8, E>>): ORDINAL
      requires Requires(i)
      reads Reads(i)
    {
      0
    }

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
      ensures |input.Produced()| == |output.Inputs()|
      ensures history == old(history) + Seq.Zip(input.Produced(), output.Inputs())
    {
      assert Valid();

      var batchWriter := new BatchSeqWriter();
      var batchWriterTotalProof := new BatchSeqWriterTotalProof(batchWriter);
      input.ForEachRemaining(batchWriter, batchWriterTotalProof);
      chunkBuffer := chunkBuffer + batchWriter.elements;
        
      var chunkProducers: seq<Producer<StreamedByte<E>>> := [];
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
        var nextChunk := Seq.Reverse(chunkBuffer[..chunkSize]);
        chunkBuffer := chunkBuffer[chunkSize..];

        var chunkProducer := ToOptionResultProducer(nextChunk);
        chunkProducers := chunkProducers + [chunkProducer];
      }

      match batchWriter.state {
      case Failure(error) =>
        var errorProducer := new SeqReader([Some(Failure(error))]);
        chunkProducers := chunkProducers + [errorProducer];
      case Success(false) =>
        if 0 < |chunkBuffer| {
          // To make it more interesting, produce an error if outputChunks is non empty?
          var nextChunk := Seq.Reverse(chunkBuffer);
          var chunkProducer := ToOptionResultProducer(nextChunk);
          outputTotalProof.AnyInputIsValid(output.history, chunkProducer);
          output.Accept(chunkProducer);
        }
      case Success(true) => {}
      }

      var producerProducer := new SeqReader(chunkProducers);
      var empty: Producer<StreamedByte<E>> := new EmptyProducer();
      var padding := new RepeatProducer(batchWriter.events as int - 1, empty);
      var concatenated: Producer<Producer<StreamedByte<E>>> := new ConcatenatedProducer(padding, producerProducer);
      concatenated.ForEachRemaining(output, outputTotalProof);

      assert |input.Produced()| == |output.Inputs()|;
      history := history + Seq.Zip(input.Produced(), output.Inputs());
    }
  }

}