include "../src/dafnyRuntime.dfy"

module MetaSeqTests {

  import opened Dafny

  trait Foo {}

  class Bar extends Foo {
    constructor() {}
  }

  method {:test} Covariance() {
    var values := new Vector<Bar>(5);
    var bar := new Bar();
    values.AddLast(bar);
    var frozenValues := values.Freeze();

    var barSeq: Sequence<Bar> := new ArraySequence<Bar>(frozenValues);
    var fooSeq: Sequence<Foo> := barSeq;
  }

}