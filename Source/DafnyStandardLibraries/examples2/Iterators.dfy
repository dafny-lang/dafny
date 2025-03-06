module ActionsExamples {
  import opened Std.Actions
  import opened Std.Producers
  import opened Std.Consumers
  import opened Std.Wrappers

  // Adapting an iterator to a producer

  iterator FibonacciIterator() yields (current: nat)
    ensures false
  {
    current := 0;
    yield;

    var prev: nat := 0;
    current := 1;
    while true {
      var next := prev + current;
      prev := current;
      current := next;
      yield;
    }
  }

  @AssumeCrossModuleTermination
  class FibonacciProducer extends IProducer<nat> {

    const iter: FibonacciIterator

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases height, 0
    {
      && this in Repr
      && iter in Repr
      && this !in iter._reads && iter._reads <= Repr
      && this !in iter._modifies && iter._modifies <= Repr
      && this !in iter._new && iter._new <= Repr
      && iter.Valid()
    }

    constructor () 
      ensures Valid()
      ensures fresh(Repr)
    {
      this.iter := new FibonacciIterator();
      new;
      Repr := {this, iter} + NonNullElements(iter._reads) + NonNullElements(iter._modifies) + NonNullElements(iter._new);
      height := 0;
    }

    function NonNullElements(s: set<object?>): set<object> {
      s - {null}
    }

    ghost predicate ValidHistory(history: seq<((), nat)>)
      decreases height
    {
      true
    }
    ghost predicate ValidInput(history: seq<((), nat)>, next: ())
      decreases height
    {
      true
    }
    twostate predicate ValidOutput(history: seq<((), nat)>, nextInput: (), new nextOutput: nat)
      decreases height
      ensures ValidOutput(history, nextInput, nextOutput) ==> ValidHistory(history + [(nextInput, nextOutput)])
    {
      ValidHistory(history + [(nextInput, nextOutput)])
    }

    method Invoke(i: ()) returns (o: nat)
      requires Requires(i)
      modifies Modifies(i)
      decreases Decreases(i).Ordinal()
      ensures Ensures(i, o)
    {
      assert Valid();
      var more := iter.MoveNext();
      assert history == old(history);
      assert more;

      o := iter.current;

      UpdateHistory(i, o);
      Repr := {this, iter} + NonNullElements(iter._reads) + NonNullElements(iter._modifies) + NonNullElements(iter._new);
    }

  }

  method PrintOutFibonnaci() {
    var iproducer := new FibonacciProducer();
    var iproducerTotalProof := new DefaultTotalActionProof(iproducer);
    var producer := new LimitedProducer(iproducer, 10, iproducerTotalProof);

    while true 
      invariant producer.Valid()
      invariant fresh(producer.Repr)
      decreases producer.Remaining()
    {
      var next := producer.Next();
      if next.None? {
        break;
      }

      print next.value, "\n";
    }
  }

  method Main() {
    PrintOutFibonnaci();
  }
}