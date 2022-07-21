include "../src/sequence.dfy"
include "../src/array.dfy"

module MetaSeqTests {

  import opened Arrays
  import opened MetaSeq

  trait Foo {}

  class Bar extends Foo {
    constructor() {}
  }

  method {:test} Covariance() {
    var values := new ResizableArray<Bar>(5);
    var bar := new Bar();
    values.AddLast(bar);
    var barSeq: Sequence<Bar> := new Direct<Bar>(values);
    var fooSeq: Sequence<Foo> := barSeq;

  }

}