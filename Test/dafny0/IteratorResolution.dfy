// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module SimplestIter {
  iterator MyIter()
}

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
    var iter := new ExampleIterator(15);
    iter.k := 12;  // error: not allowed to assign to iterator's in-parameters
    iter.x := 12;  // allowed (but this destroys the validity of 'iter'
    iter.xs := [];  // error: not allowed to assign to iterator's yield-history variables
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

  method StaticM(k: nat) returns (m: int)
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
      var it := new ExampleIterator(100);
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
      g0.u := true;  // allowed (but this destroys the validity of 'iter'
      var g1 := new GenericIterator(20);
      assert g1.u < 200;  // .u is an integer

      assert g2.u == 200;  // error: the type parameter of g2 is unknown

      var h0 := new GenericIteratorResult._ctor();
      // so far, the instantiated type of h0 is unknown
      var k := h0.t;
      assert k < 87;

      var h1 := new GenericIteratorResult();
      // so far, the instantiated type of h1 is unknown
      if (*) {
        var b: bool := h1.t;  // this determines h1 to be of type GenericIteratorResult<bool>
      } else {
        var x: int := h1.t;  // error: h1 would have to be a GenericIteratorResult<int>
      }

      var h2 := new GenericIteratorResult;  // error: constructor is not mentioned

      var h3 := new GenericIterator._ctor(30);
      if (h3.t == h3.u) {
        assert !h3.t;  // error: type mismatch
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

// --------------------------------- _decreases<n> fields

module DecreasesFields {
  class Cell
  {
    var data: int;
  }

  iterator Dieter0(c: Cell)
    requires c != null;
    decreases c.data, c.data, c != null;
  {
    assert _decreases0 == _decreases1;
    assert _decreases2;
    assert _decreases3 == null;  // error: there is no _decreases3
    assert _decreases0 == null;  // error: type mismatch
    _decreases2 := false;  // error: the field is immutable
  }

  iterator Dieter1(c: Cell)
    requires c != null;
  {
    assert _decreases0 == c;
    assert _decreases1;  // error: there is no _decreases1
  }

  iterator Dieter2()
  {
    assert _decreases0 == null;  // error: there is no _decreases0
  }
}
