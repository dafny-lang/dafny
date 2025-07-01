module ActionsExamples {
  import opened Std.Actions
  import opened Std.ActionsExterns
  import opened Std.BulkActions
  import opened Std.BoundedInts
  import opened Std.Producers
  import opened Std.Consumers
  import opened Std.Wrappers
  import opened Std.Frames
  import opened Std.Termination

  // Demonstrating the simplest idiom
  // for looping over the values produced by a Producer<T>
  method {:test} SimpleProducerLoop() {
    var p := MakeProducer();
    while true
      invariant p.Valid()
      invariant fresh(p.Repr)
      decreases p.Decreasing()
    {
      var next := p.Next();
      if next.None? {
        break;
      }

      expect 0 < next.value <= 5;
    }
  }

  method MakeProducer() returns (p: Producer<nat>)
    ensures p.Valid()
    ensures fresh(p.Repr)
  {
    var s: seq<nat> := [1, 2, 3, 4, 5];
    p := new SeqReader(s);
  }

  // Demonstration that actions can consume/produce reference values as well,
  // despite the usual challenges of quantifying over such types.

  class Box {
    const i: nat

    constructor(i: nat)
      ensures this.i == i
      reads {}
    {
      this.i := i;
    }
  }

  function SeqRange(n: nat): seq<nat> {
    seq(n, i => i)
  }

  lemma SeqRangeIncr(prefix: seq<nat>, n: nat)
    requires prefix == SeqRange(n)
    ensures prefix + [n] == SeqRange(n + 1)
  {}

  @AssumeCrossModuleTermination
  class BoxEnumerator extends Action<(), Box> {

    var nextValue: nat

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases Repr, 0
    {
      && this in Repr
      && ValidHistory(history)
      && nextValue == |history|
    }

    twostate predicate ValidChange()
      reads this, Repr
      ensures ValidChange() ==>
                old(Valid()) && Valid() && fresh(Repr - old(Repr))
      ensures ValidChange() ==> old(history) <= history
    {
      && old(Valid()) && Valid()
      && fresh(Repr - old(Repr))
      && old(history) <= history
    }

    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()
    {}

    constructor ()
      ensures Valid()
      ensures fresh(Repr)
      ensures history == []
    {
      nextValue := 0;
      history := [];
      Repr := {this};
    }

    ghost predicate ValidInput(history: seq<((), Box)>, next: ())
      requires ValidHistory(history)
      decreases Repr
    {
      true
    }
    ghost predicate ValidHistory(history: seq<((), Box)>)
      decreases Repr
    {
      Seq.Map((b: Box) => b.i, OutputsOf(history)) == SeqRange(|history|)
    }

    ghost function Decreases(t: ()): ORDINAL
      reads Reads(t)
    {
      ReprTerminationMetric().Ordinal()
    }

    method Invoke(t: ()) returns (r: Box)
      requires Requires(t)
      reads Repr
      modifies Modifies(t)
      decreases Decreases(t), 0
      ensures Ensures(t, r)
    {
      assert Requires(t);
      ghost var producedBefore := Outputs();

      r := new Box(nextValue);
      UpdateHistory(t, r);
      Repr := {this};
      nextValue := nextValue + 1;

      SeqRangeIncr(Seq.Map((b: Box) => b.i, producedBefore), |producedBefore|);
      assert Valid();
    }
  }

  method BoxEnumeratorExample() {
    var enum: BoxEnumerator := new BoxEnumerator();
    assert |enum.Outputs()| == 0;
    var a := enum.Invoke(());

    assert enum.Outputs() == [a];
  }

  @IsolateAssertions
  @ResourceLimit("10e6")
  method ConsumerExample() {
    var a: DynamicArrayWriter<nat> := new DynamicArrayWriter();
    var _ := a.Invoke(1);
    var _ := a.Invoke(2);
    var _ := a.Invoke(3);
    var _ := a.Invoke(4);
    var _ := a.Invoke(5);
    assert a.Inputs() == [1, 2, 3, 4, 5];
    assert a.storage.items == [1, 2, 3, 4, 5];
  }

  // The dual of Producer.ForEach(IConsumer),
  // which terminates when the consumer runs out of capacity
  // instead of when the producer runs out of elements.
  // Not defined on Consumer because that would create
  // a cycle between the modules.
  // 
  // It is interesting to note that this version will
  // "waste" one of the produced elements,
  // since there is no way to query the consumer
  // to see if it will accept the next element.
  // One could imagine a different setup
  // where the consumer provides a predicate for
  // whether it will accept the next element,
  // which would be related therefore to ValidInput().
  @IsolateAssertions
  method Fill<T>(producer: IProducer<T>, ghost producerTotalProof: TotalActionProof<(), T>,
                 consumer: Consumer<T>, ghost consumerTotalProof: TotalActionProof<T, bool>)
    requires producer.Valid()
    requires consumer.Valid()
    requires producerTotalProof.Valid()
    requires producerTotalProof.Action() == producer
    requires consumerTotalProof.Valid()
    requires consumerTotalProof.Action() == consumer
    requires producer.Repr !! consumer.Repr !! producerTotalProof.Repr !! consumerTotalProof.Repr
    modifies producer.Repr, consumer.Repr
  {
    while true
      invariant producer.ValidAndDisjoint()
      invariant consumer.ValidAndDisjoint()
      invariant producerTotalProof.Valid()
      invariant consumerTotalProof.Valid()
      invariant producer.Repr !! consumer.Repr
      decreases consumer.Decreasing()
    {
      producerTotalProof.AnyInputIsValid(producer.history, ());
      var t := producer.Next();

      consumerTotalProof.AnyInputIsValid(consumer.history, t);
      var more := consumer.Accept(t);
      if !more {
        break;
      }
    }
  }

  @AssumeCrossModuleTermination
  class Splitter extends OutputterOfNewProducers<nat, nat> {

    constructor ()
      ensures Valid()
      ensures fresh(Repr)
      ensures history == []
    {
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
      && ValidHistory(history)
    }

    twostate predicate ValidChange()
      reads this, Repr
      ensures ValidChange() ==> old(Valid()) && Valid()
      ensures ValidChange() ==> fresh(Repr - old(Repr))
      ensures ValidChange() ==> old(history) <= history
      decreases Repr, 0
    {
      && old(Valid())
      && Valid()
      && fresh(Repr - old(Repr))
      && old(history) <= history
    }

    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()
    {}

    ghost predicate ValidHistory(history: seq<(nat, Producer<nat>)>)
      decreases Repr
    {
      true
    }
    ghost predicate ValidInput(history: seq<(nat, Producer<nat>)>, next: nat)
      requires ValidHistory(history)
      decreases Repr
    {
      true
    }

    lemma AnyInputIsValid(history: seq<(nat, Producer<nat>)>, next: nat)
      requires Valid()
      requires Action().ValidHistory(history)
      ensures Action().ValidInput(history, next)
    {}

    ghost function MaxProduced(): TerminationMetric
    {
      TMTop
    }

    ghost function Decreases(i: nat): ORDINAL
      requires Valid()
      reads this, Repr
      decreases Repr, 3
    {
      0
    }

    method Invoke(x: nat) returns (result: Producer<nat>)
      requires Requires(x)
      reads Repr
      modifies Modifies(x)
      decreases Decreases(x), 0
      ensures Ensures(x, result)
      ensures OutputFresh(result)
    {
      result := new SeqReader<nat>([x / 2, x - (x / 2)]);
      UpdateHistory(x, result);
      MaxProduced().TopDecreasesToNat(result.DecreasesMetric());
    }
  }

  @IsolateAssertions
  method {:test} ExamplePipeline() {
    var input := new SeqReader<nat>([1, 2, 3, 4, 5]);
    var splitter := new Splitter();
    var mapped := new MappedProducerOfNewProducers(input, splitter);
    var flattened := new FlattenedProducer(mapped);

    var collector := new SeqWriter();

    var collectorTotalProof := new DefaultTotalActionProof(collector);
    flattened.ForEach(collector, collectorTotalProof);

    expect collector.values == [0, 1, 1, 1, 1, 2, 2, 2, 2, 3], collector.values;
  }

  // "Batched Byte"
  type BB = Batched<uint8, string>

  // TODO - not verifying yet
  // @AssumeCrossModuleTermination
  // class Chunker extends BulkAction<BB, Producer<BB>>, OutputterOfNewProducers<BB, BB> {

  //   const chunkSize: nat
  //   var chunkBuffer: seq<uint8>

  //   constructor(chunkSize: nat)
  //     requires 0 < chunkSize
  //     ensures Valid()
  //     ensures fresh(Repr)
  //     ensures history == []
  //   {
  //     this.chunkSize := chunkSize;
  //     chunkBuffer := [];
  //     history := [];
  //     Repr := {this};
  //   }

  //   ghost predicate Valid()
  //     reads this, Repr
  //     ensures Valid() ==> this in Repr
  //     ensures Valid() ==> ValidHistory(history)
  //     decreases Repr, 0
  //   {
  //     && this in Repr
  //     && 0 < chunkSize
  //   }

  //   twostate predicate ValidChange()
  //     reads this, Repr
  //     ensures ValidChange() ==> old(Valid()) && Valid()
  //     ensures ValidChange() ==> fresh(Repr - old(Repr))
  //     ensures ValidChange() ==> old(history) <= history
  //   {
  //     && fresh(Repr - old(Repr))
  //     && old(Valid())
  //     && Valid()
  //     && old(history) <= history
  //   }

  //   twostate lemma ValidImpliesValidChange()
  //     requires old(Valid())
  //     requires unchanged(old(Repr))
  //     ensures ValidChange()
  //   {}

  //   ghost predicate ValidHistory(history: seq<(BB, Producer<BB>)>)
  //     decreases Repr
  //   {
  //     true
  //   }

  //   ghost predicate ValidInput(history: seq<(BB, Producer<BB>)>, next: BB)
  //     requires ValidHistory(history)
  //     decreases Repr
  //   {
  //     true
  //   }

  //   ghost function Decreases(i: BB): ORDINAL
  //     requires Requires(i)
  //     reads Reads(i)
  //   {
  //     0
  //   }

  //   ghost function MaxProduced(): TerminationMetric {
  //     TMTop
  //   }

  //   lemma AnyInputIsValid(history: seq<(BB, Producer<BB>)>, next: BB)
  //     requires Valid()
  //     requires Action().ValidHistory(history)
  //     ensures Action().ValidInput(history, next)
  //   {}

  //   @IsolateAssertions
  //   method Invoke(i: BB) returns (o: Producer<BB>)
  //     requires Requires(i)
  //     reads Reads(i)
  //     modifies Modifies(i)
  //     decreases Decreases(i), 0
  //     ensures Ensures(i, o)
  //     ensures OutputFresh(o)
  //   {
  //     assert Valid();
  //     var input := new SeqReader([i]);
  //     var output := new SeqWriter();
  //     ghost var outputTotalProof := new SeqWriterTotalActionProof(output);
  //     ghost var thisTotalProof := new ChunkerTotalProof(this);
  //     label before:
  //     Map(input, output, thisTotalProof, outputTotalProof);
  //     assert |output.values| == 1;
  //     o := output.values[0];
  //     assert Seq.Last(output.Inputs()) == o;
  //     assert Seq.Last(Inputs()) == i;
  //   }

  //   @ResourceLimit("1e9")
  //   @IsolateAssertions
  //   method Map(input: Producer<BB>,
  //              output: IConsumer<Producer<BB>>,
  //              ghost thisTotalProof: TotalActionProof<BB, Producer<BB>>,
  //              ghost outputTotalProof: TotalActionProof<Producer<BB>, ()>)
  //     requires Valid()
  //     requires input.Valid()
  //     requires output.Valid()
  //     requires outputTotalProof.Valid()
  //     requires outputTotalProof.Action() == output
  //     requires Repr !! input.Repr !! output.Repr !! outputTotalProof.Repr
  //     reads this, Repr, input, input.Repr, output, output.Repr, thisTotalProof, thisTotalProof.Repr, outputTotalProof, outputTotalProof.Repr
  //     modifies Repr, input.Repr, output.Repr, outputTotalProof.Repr
  //     ensures ValidChange()
  //     ensures input.ValidChange()
  //     ensures output.ValidChange()
  //     ensures input.Done()
  //     ensures input.NewProduced() == NewInputs()
  //     ensures |input.NewProduced()| == |output.NewInputs()|
  //     ensures output.NewInputs() == NewOutputs()
  //     ensures forall o <- NewOutputs() :: OutputFresh(o)
  //   {
  //     assert Valid();

  //     var oldProducedCount := input.ProducedCount();
  //     var batchWriter := new BatchSeqWriter();
  //     var batchWriterTotalProof := new BatchSeqWriterTotalProof(batchWriter);
  //     label before:
  //     input.ForEach(batchWriter, batchWriterTotalProof);
  //     label after:
  //     assert input.ValidChange@before();
  //     assert input.ValidChange();
  //     input.ProducedAndNewProduced@before();

  //     var newProducedCount := input.ProducedCount() - oldProducedCount;
  //     assert newProducedCount == input.NewProducedCount();
  //     if newProducedCount == 0 {
  //       // No-op
  //       assert input.ValidChange();
  //       assert |batchWriter.Inputs()| == 0;
  //       assert input.NewProduced() == batchWriter.Inputs();
  //       assert |input.NewProduced()| == 0;
  //       output.ValidImpliesValidChange();
  //       return;
  //     }

  //     chunkBuffer := chunkBuffer + batchWriter.elements;

  //     var chunks, leftover := Chunkify(chunkBuffer);
  //     chunkBuffer := leftover;

  //     var outputProducer: Producer<BB>;
  //     match batchWriter.state {
  //       case Failure(error) =>
  //         outputProducer := new SeqReader([BatchError(error)]);
  //       case Success(more) =>
  //         if !more && 0 < |chunkBuffer| {
  //           // To make it more interesting, produce an error if outputChunks is non empty?
  //           chunks := chunks + Seq.Reverse(chunkBuffer);
  //           chunkBuffer := [];
  //         }
  //         outputProducer := new BatchReader(chunks);
  //     }

  //     var empty := new EmptyProducer();
  //     var padding: Producer<Producer<BB>> := new RepeatProducer(newProducedCount - 1, empty);
  //     var producerProducer := new SeqReader([outputProducer]);
  //     var concatenated: Producer<Producer<BB>> := new ConcatenatedProducer(padding, producerProducer);
  //     assert producerProducer.Remaining() == Some(1);
  //     assert padding.Remaining() == Some(newProducedCount - 1);
  //     assert concatenated.Remaining() == Some(newProducedCount);
  //     label beforeOutput:
  //     concatenated.ForEach(output, outputTotalProof);
  //     assert concatenated.ValidChange@beforeOutput();
  //     concatenated.ProducedAndNewProduced@beforeOutput();

  //     assert |input.NewProduced()| == newProducedCount;
  //     assert |concatenated.NewProduced@beforeOutput()| == newProducedCount;
  //     assert |input.NewProduced()| == |output.NewInputs()|;
  //     history := history + Seq.Zip(input.NewProduced(), output.NewInputs());
  //     assert input.NewProduced() == NewInputs();
  //   }

  //   method Chunkify(data: seq<uint8>) returns (chunks: seq<uint8>, leftover: seq<uint8>)
  //     reads this, Repr
  //     requires Valid()
  //   {
  //     leftover := data;
  //     chunks := [];
  //     while chunkSize as int <= |leftover|
  //       decreases |leftover|
  //     {
  //       chunks := chunks + Seq.Reverse(leftover[..chunkSize]);
  //       leftover := leftover[chunkSize..];
  //     }
  //   }
  // }

  // @AssumeCrossModuleTermination
  // class ChunkerTotalProof extends TotalActionProof<BB, Producer<BB>> {

  //   ghost const chunker: Chunker

  //   ghost constructor(chunker: Chunker)
  //     requires chunker.Valid()
  //     reads {}
  //     ensures this.chunker == chunker
  //     ensures Valid()
  //     ensures fresh(Repr)
  //   {
  //     this.chunker := chunker;
  //     Repr := {this};
  //   }

  //   ghost function Action(): Action<BB, Producer<BB>> {
  //     chunker
  //   }

  //   ghost predicate Valid()
  //     reads this, Repr
  //     ensures Valid() ==> this in Repr
  //     decreases Repr, 0
  //   {
  //     this in Repr
  //   }

  //   twostate predicate ValidChange()
  //     reads this, Repr
  //     ensures ValidChange() ==>
  //               old(Valid()) && Valid() && fresh(Repr - old(Repr))
  //   {
  //     old(Valid()) && Valid() && fresh(Repr - old(Repr))
  //   }

  //   twostate lemma ValidImpliesValidChange()
  //     requires old(Valid())
  //     requires unchanged(old(Repr))
  //     ensures ValidChange()
  //   {}

  //   lemma AnyInputIsValid(history: seq<(BB, Producer<BB>)>, next: BB)
  //     requires Valid()
  //     requires Action().ValidHistory(history)
  //     ensures Action().ValidInput(history, next)
  //   {}
  // }
}