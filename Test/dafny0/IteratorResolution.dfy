iterator MyIter()

module Mx {

  iterator ExampleIterator(k: int) yields (x: int, y: int)
  {
    var i := k;
    while (true) {
      if (i % 77 == 0) { yield; }
      yield i, -i;
      i := i + 1;
    }
  }

  method IteratorUser() {
    var iter := new ExampleIterator.ExampleIterator(15);
    var j := 0;
    while (j < 100) {
      var more := iter.MoveNext();
      if (!more) {
        break;
      }
      print iter.x, iter.y;
      j := j + 1;
    }
  }

  static method StaticM(k: nat) returns (m: int)
  {
    m := k;
  }

  module Inner {
    iterator YetAnother(x: int, y: int, z: int) yields (a: bool, b: bool)
      requires true;
  }

  class Client {
    method M() {
      var m := StaticM(5);
      var it := new ExampleIterator.ExampleIterator(100);
      var a, b := Worker(it);
    }
    method Worker(xi: ExampleIterator) returns (k: int, m: int) {
      k, m := xi.k + xi.x, xi.y;
      var mr := xi.MoveNext();
      if (mr) {
        k := xi.x;
      } else {
        assert k == xi.k + xi.x && m == xi.y;
      }
    }
    method GenericTester(g0: GenericIterator<bool>, g2: GenericIterator)
      requires g0.u;
    {
      g0.t := true;  // error: not allowed to assign to .t
      g0.u := true;  // error: not allowed to assign to .u
      var g1 := new GenericIterator.GenericIterator(20);
      assert g1.u < 200;  // .u is an integer

      assert g2.u == 200;  // error: the type parameter of g2 is unknown

      var h0 := new GenericIteratorResult.GenericIteratorResult();
      // so far, the instantiated type of h0 is unknown
      var k := h0.t;
      assert k < 87;

      var h1 := new GenericIteratorResult.GenericIteratorResult();
      // so far, the instantiated type of h1 is unknown
      if (*) {
        var b: bool := h1.t;  // this determines h1 to be of type GenericIteratorResult<bool>
      } else {
        var x: int := h1.t;  // error: h1 would have to be a GenericIteratorResult<int>
      }
    }
  }

  iterator GenericIterator<T>(t: T) yields (u: T)
  {
    while (true) {
      yield t;
    }
  }

  iterator GenericIteratorResult<T>() yields (t: T)
  {
    while (*) { yield; }
  }

  class AnotherClient {
    method StaticM(b: bool) // [sic]
    {
    }
    method Q() {
      StaticM(true);  // this is supposed to resolve to AnotherClient.StaticM, not _default.StaticM
    }
  }
}
