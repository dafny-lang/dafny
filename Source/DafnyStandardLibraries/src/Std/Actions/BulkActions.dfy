module Std.BulkActions {

  import opened Actions
  import opened Consumers
  import opened Producers
  import opened Wrappers
  import opened BoundedInts
  import opened Termination

  // A wrapper type useful as the output type of producers that may encounter errors.
  // Equivalent to Option<Result<T, E>> but generally more readable.
  datatype Batched<T, E> = BatchValue(value: T) | BatchError(error: E) | EndOfInput
  type BatchedByte<E> = Batched<uint8, E>

  @AssumeCrossModuleTermination
  trait BulkAction<I, O> extends Action<I, O> {

    method Map(input: Producer<I>, output: IConsumer<O>,
               ghost thisTotalProof: TotalActionProof<I, O>, ghost outputTotalProof: TotalActionProof<O, ()>)
      requires Valid()
      requires input.Valid()
      requires output.Valid()
      requires thisTotalProof.Valid()
      requires thisTotalProof.Action() == this
      requires outputTotalProof.Valid()
      requires outputTotalProof.Action() == output
      requires Repr !! input.Repr !! output.Repr !! thisTotalProof.Repr !! outputTotalProof.Repr
      reads this, Repr, input, input.Repr, output, output.Repr, thisTotalProof, thisTotalProof.Repr, outputTotalProof, outputTotalProof.Repr
      modifies Repr, input.Repr, output.Repr, outputTotalProof.Repr
      ensures ValidChange()
      ensures input.ValidChange()
      ensures output.ValidChange()
      ensures input.Done()
      ensures |input.NewProduced()| == |output.NewInputs()|
      ensures history == old(history) + Seq.Zip(input.NewProduced(), output.NewInputs())
  }

  /**
    * The equivalent of MappedProducer(ToBatched, SeqReader(elements)),
    * but a separate class so it's possible to optimize via "is" testing.
    */
  @AssumeCrossModuleTermination
  class BatchReader<T, E> extends Producer<Batched<T, E>> {

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
      && Produced() == Seq.Map(ToBatched, elements[..index])
      && |Produced()| == index
      && (index < |elements| ==> Seq.All(Outputs(), IsSome))
    }

    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()
    {}

    ghost predicate ValidOutputs(outputs: seq<Option<Batched<T, E>>>)
      requires Seq.Partitioned(outputs, IsSome)
      decreases Repr
    {
      true
    }

    function ProducedCount(): nat
      requires Valid()
      reads this, Repr
      ensures ProducedCount() == |Produced()|
    {
      index
    }

    function Remaining(): Option<nat>
      reads this, Repr
      requires Valid()
    {
      Some(|elements| - index)
    }


    ghost function DecreasesMetric(): TerminationMetric
      requires Valid()
      reads this, Repr
      decreases Repr, 3
    {
      TMNat(|elements| - index)
    }

    @IsolateAssertions
    method Invoke(t: ()) returns (value: Option<Batched<T, E>>)
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
        value := Some(BatchValue(elements[index]));

        OutputsPartitionedAfterOutputtingSome(value.value);
        ProduceSome(value.value);
        index := index + 1;
      }

      assert Valid();
      assert ValidChange();
    }

    @IsolateAssertions
    method ForEach(consumer: IConsumer<Batched<T, E>>, ghost totalActionProof: TotalActionProof<Batched<T, E>, ()>)
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
        assert NewProduced() == Seq.Map(ToBatched, s);

        writer.elements := writer.elements + s;
        writer.history := writer.history + Seq.Zip(NewProduced(), Seq.Repeat((), |s|));

        return;
      }

      DefaultForEach(this, consumer, totalActionProof);
    }

    method Fill(consumer: Consumer<Batched<T, E>>, ghost totalActionProof: TotalActionProof<Batched<T, E>, bool>)
      requires Valid()
      requires consumer.Valid()
      requires consumer.Capacity().Some?
      requires Repr !! consumer.Repr !! totalActionProof.Repr
      requires totalActionProof.Valid()
      requires totalActionProof.Action() == consumer
      modifies Repr, consumer.Repr
      ensures ValidChange()
      ensures consumer.ValidChange()
      ensures Done() || consumer.Capacity() == Some(0)
      ensures NewProduced() == consumer.NewConsumed()
    {
      DefaultFill(this, consumer, totalActionProof);
    }

    @IsolateAssertions
    method Read() returns (s: seq<T>)
      requires Valid()
      reads this, Repr
      modifies Repr
      ensures ValidAndDisjoint()
      ensures Done()
      ensures ValidChange()
      ensures NewProduced() == Seq.Map(ToBatched, s)
    {
      // Avoid the slice if possible
      if index == 0 {
        s := elements;
      } else {
        s := elements[index..];
      }
      index := |elements|;

      var produced := Seq.Map(ToBatched, s);
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
  class BatchSeqWriter<T, E> extends IConsumer<Batched<T, E>> {

    var elements: seq<T>
    var state: Result<bool, E>

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
    }

    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()
    {}

    ghost predicate ValidHistory(history: seq<(Batched<T, E>, ())>)
      decreases Repr
    {
      true
    }
    ghost predicate ValidInput(history: seq<(Batched<T, E>, ())>, next: Batched<T, E>)
      requires ValidHistory(history)
      decreases Repr
    {
      true
    }

    ghost function Decreases(t: Batched<T, E>): ORDINAL
      reads Reads(t)
    {
      0
    }

    @IsolateAssertions
    method Invoke(t: Batched<T, E>) returns (r: ())
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
        case BatchValue(t) => elements := elements + [t];
        case BatchError(e) => state := Failure(e);
        case EndOfInput => state := Success(false);
      }
      r := ();

      UpdateHistory(t, r);

      assert Valid();
    }

    function Values(): seq<T>
      requires Valid()
      reads this, Repr
    {
      elements
    }
  }

  @AssumeCrossModuleTermination
  class BatchSeqWriterTotalProof<T, E> extends TotalActionProof<Batched<T, E>, ()> {
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
      ensures ValidChange() ==>
                old(Valid()) && Valid() && fresh(Repr - old(Repr))
      decreases Repr, 0
    {
      old(Valid()) && Valid() && fresh(Repr - old(Repr))
    }

    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()
    {}

    ghost function Action(): Action<Batched<T, E>, ()> {
      action
    }

    lemma AnyInputIsValid(history: seq<(Batched<T, E>, ())>, next: Batched<T, E>)
      requires Valid()
      requires Action().ValidHistory(history)
      ensures Action().ValidInput(history, next)
    {}
  }

  @AssumeCrossModuleTermination
  class BatchArrayWriter<T, E> extends Consumer<Batched<T, E>> {

    var storage: array<T>
    var size: nat
    var otherInputs: nat
    var state: Result<bool, E>

    constructor(storage: array<T>)
      ensures Valid()
      ensures history == []
      ensures fresh(Repr - {storage})
      reads {}
      ensures this.storage == storage
      ensures state == Success(true)
    {
      this.storage := storage;
      this.size := 0;
      this.otherInputs := 0;
      this.state := Success(true);

      Repr := {this, storage};
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
      && storage in Repr
      && size + otherInputs <= storage.Length
      && (Done() ==> size + otherInputs == storage.Length)
      && |Consumed()| == size + otherInputs
      && (size + otherInputs < storage.Length ==> Seq.All(history, WasConsumed))
    }

    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()
    {}

    ghost predicate ValidInput(history: seq<(Batched<T, E>, bool)>, next: Batched<T, E>)
      requires ValidHistory(history)
      decreases Repr
    {
      true
    }

    ghost function DecreasesMetric(): TerminationMetric
      requires Valid()
      reads this, Repr
      decreases Repr, 3
    {
      TMNat(storage.Length - size - otherInputs)
    }

    function Capacity(): Option<nat>
      reads this, Repr
      requires Valid()
    {
      Some(storage.Length - size - otherInputs)
    }

    @IsolateAssertions
    method Invoke(t: Batched<T, E>) returns (r: bool)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t), 0
      ensures Ensures(t, r)
      ensures DecreasedBy(r)
    {
      assert Requires(t);
      assert Valid();
      reveal TerminationMetric.Ordinal();

      if size + otherInputs == storage.Length {
        r := false;

        UpdateHistory(t, r);
        Seq.PartitionedCompositionRight(old(history), [(t, false)], WasConsumed);
        ConsumedComposition(old(history), [(t, r)]);
      } else {
        match t {
          case BatchValue(value) =>
            storage[size] := value;
            size := size + 1;
          case BatchError(e) =>
            state := Failure(e);
            otherInputs := otherInputs + 1;
          case EndOfInput =>
            state := Success(false);
            otherInputs := otherInputs + 1;
        }
        r := true;

        UpdateHistory(t, r);
        Seq.PartitionedCompositionLeft(old(history), [(t, true)], WasConsumed);
        ConsumedComposition(old(history), [(t, r)]);
        calc {
          |Consumed()|;
          old(|Consumed()|) + |ConsumedOf([(t, r)])|;
          old(size + otherInputs) + 1;
          size + otherInputs;
        }
      }

      assert Valid();
      assert ValidChange();
    }

    function Values(): seq<T>
      requires Valid()
      reads this, Repr
    {
      storage[..size]
    }
  }

  @AssumeCrossModuleTermination
  class BatchArrayWriterTotalProof<T, E> extends TotalActionProof<Batched<T, E>, bool> {
    ghost const action: BatchArrayWriter<T, E>

    ghost constructor (action: BatchArrayWriter<T, E>)
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
      ensures ValidChange() ==>
                old(Valid()) && Valid() && fresh(Repr - old(Repr))
      decreases Repr, 0
    {
      old(Valid()) && Valid() && fresh(Repr - old(Repr))
    }

    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()
    {}

    ghost function Action(): Action<Batched<T, E>, bool> {
      action
    }

    lemma AnyInputIsValid(history: seq<(Batched<T, E>, bool)>, next: Batched<T, E>)
      requires Valid()
      requires Action().ValidHistory(history)
      ensures Action().ValidInput(history, next)
    {}
  }

  function ToBatched<T, E>(t: T): Batched<T, E> {
    BatchValue(t)
  }

  method ToBatchedProducer<T, E>(values: seq<T>) returns (result: Producer<Batched<T, E>>)
    reads {}
    ensures result.Valid()
    ensures fresh(result.Repr)
    ensures result.history == []
  {
    var chunkProducer := new SeqReader(values);
    var mapping := new FunctionAction(ToBatched);
    var mappingTotalProof := new TotalFunctionActionProof(mapping, ToBatched);
    result := new MappedProducer(chunkProducer, mapping, mappingTotalProof);
  }
}