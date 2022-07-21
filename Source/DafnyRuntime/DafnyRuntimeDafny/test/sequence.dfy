include "../src/sequence.dfy"
include "../src/array.dfy"

module MetaSeqTests {

  import opened Arrays
  import opened Sequences

  trait Foo {}

  class Bar extends Foo {
    constructor() {}
  }

  method {:test} Covariance() {
    var values := new ResizableArray<Bar>(5);
    var bar := new Bar();
    values.AddLast(bar);
    var frozenValues := values.Freeze();

    var barSeq: Sequence<Bar> := new ArraySequence<Bar>(frozenValues);
    var fooSeq: Sequence<Foo> := barSeq;
  }

}