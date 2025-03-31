// RUN: %exits-with 2 %verify --type-system-refresh=false --general-newtypes=false "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module SimplestIter {
  iterator MyIter()
}

module Mx {

  iterator ExampleIterator(k: int) yields (x: int, y: int)
  {
    var i := k;
    while true {
      if i % 77 == 0 { yield; }
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
    while j < 100 {
      var more := iter.MoveNext();
      if !more {
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
      requires true
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
      if mr {
        k := xi.x;
      } else {
        assert k == xi.k + xi.x && m == xi.y;
      }
    }
    method GenericTester(g0: GenericIterator<bool>, g2: GenericIterator)
      requires g0.u
    {
      g0.t := true;  // error: not allowed to assign to .t
      g0.u := true;  // allowed (but this destroys the validity of 'iter'
      var g1 := new GenericIterator(20);
      assert g1.u < 200;  // .u is an integer

      assert g2.u == 200;  // error: the type parameter of g2 is unknown

      var h0 := new GenericIteratorResult();
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

      var h3 := new GenericIterator(30);  // see two lines down
      if h3.t == h3.u {
        assert !h3.t;  // error: type mismatch (here or two lines ago)
      }
    }
  }

  iterator GenericIterator<T(0)>(t: T) yields (u: T)
  {
    while true {
      yield t;
    }
  }

  iterator GenericIteratorResult<T(0)>() yields (t: T)
  {
    while * {
      yield;
    }
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
    var data: int
  }

  iterator Dieter0(c: Cell)
    requires c != null
    decreases c.data, c.data, c != null
  {
    assert _decreases0 == _decreases1;
    assert _decreases2;
    assert _decreases3 == null;  // error: there is no _decreases3
    assert _decreases0 == null;  // error: type mismatch
    _decreases2 := false;  // error: the field is immutable
  }

  iterator Dieter1(c: Cell)
    requires c != null
  {
    assert _decreases0 == c;
    assert _decreases1;  // error: there is no _decreases1
  }

  iterator Dieter2()
  {
    assert _decreases0 == null;  // error: there is no _decreases0
  }
}

// ---------- iterator (and other) type parameters -------------------------------

module IteratorTypeParameters {
  type Five = x | 5 <= x ghost witness 6
  type Six = x | 6 <= x ghost witness 6
  codatatype Stream = More(r: real, s: Stream)

  class MyClass<A(==),B(0)> {
  }
  method TestClass() {
    var ma := new MyClass<Stream,int>;  // error (x2): cannot pass in Stream as type parameter A(==)
    var mb := new MyClass<Five,Six>;  // error (x2): cannot pass in Six as type parameter B(0)
  }

  class ClassWithConstructorX<A(==),B(0)> {
    constructor Init() { }
  }
  method TestClassWCX() {
    var ma := new ClassWithConstructorX<Stream,int>.Init();  // error (x2): cannot pass in Stream as type parameter A(==)
    var mb := new ClassWithConstructorX<Five,Six>.Init();  // error (x2): cannot pass in Six as type parameter B(0)
  }

  class ClassWithConstructorY {
    constructor Init<A(==),B(0)>() { }
  }
  method TestClassWCY() {
    var ma := new ClassWithConstructorY.Init<Stream,int>();  // error: cannot pass in Stream as type parameter A(==)
    var mb := new ClassWithConstructorY.Init<Five,Six>();  // error: cannot pass in Six as type parameter B(0)
  }

  method MyMethod<A(==),B(0)>() { }
  method TestMethod() {
    MyMethod<Stream,int>();  // error: cannot pass in Stream as type parameter A(==)
    MyMethod<Five,Six>();  // error: cannot pass in Six as type parameter B(0)
  }

  function MyFunction<A(==),B(0)>(): int { 65 }
  method TestFunction() {
    var x := MyFunction<Stream,int>();  // error: cannot pass in Stream as type parameter A(==)
    var y := MyFunction<Five,Six>();  // error: cannot pass in Six as type parameter B(0)
  }

  iterator MyIter<A(0,==), B(0)>(a: A) yields (b: B)
    ensures false  // never ends
  {
    while true
    {
      yield;  // notice that "b" has not been explicitly initialized
    }
  }

  method GoodClient() {
    var iter := new MyIter<char,nat>('i');
    var n := iter.b;  // this could be bad, if "b" has not been properly initialized
    assert 0 <= n;  // this is what would go wrong (false at run time, but undetected by verifier)
    var i := 0;
    while i < n {
      var more := iter.MoveNext();
      assert more;  // the iterator never ends
      i := i + 1;
    }
  }

  method DisallowedClientA() {
    if * {
      var s;
      var iter := new MyIter<Stream,int>(s);  // error (x2): cannot instantiate iterator with Stream for A(==)
    } else if * {
      var s: Stream;
      var iter := new MyIter(s);  // error (x2): cannot instantiate iterator with Stream for A(==)
      assert iter.b <= 0 || 0 <= iter.b;
    } else if * {
      var s: Stream;
      var o: object := new MyIter<Stream,int>(s);  // error: cannot instantiate iterator with Stream for A(==)
      var p: object := new MyIter<char,Six>('g');  // error: cannot instantiate iterator with Six for B(0)
    } else if * {
      var iter: MyIter<Stream,int>;  // error: even this variable declaration is disallowed
    } else if * {
      var arr := new int[25]; var somethingToCompareWith: object;
      forall iter: MyIter<Stream,int> | iter == somethingToCompareWith {  // error: even this variable declaration is disallowed
        arr[2] := 60;
      }
    } else {
      var bl: bool := forall iter: MyIter<Stream,int> | iter in {} :: true;  // error (x2): ditto
    }
  }

  method DisallowedClientB() {
    var iter := new MyIter<Five,Six>(12);  // error (x2): cannot instantiate iterator with Five or Six
    var n := iter.b;  // this could be bad, if "b" has not been properly initialized
    assert 6 <= n;  // this is what would go wrong (false at run time, but undetected by verifier)
    var i := 0;
    while i < n
      invariant iter.a == 12
    {
      var more := iter.MoveNext();
      assert more;  // the iterator never ends
      assert 6 <= iter.b;  // the verifier thinks this is okay, but it wouldn't be at run time, if this were allowed
      i := i + 1;
    }
  }

  iterator AnotherIter<A(==,0), B(==,0)>(a: A) yields (b: B)
    ensures false  // never ends
  {
    while true
    {
      yield;  // notice that "b" has not been explicitly initialized
    }
  }

  method AnotherClient() {
    if * {
      var iter := new AnotherIter<real,Stream>(3.2);  // error (x2): cannot pass in Stream as B(==)
    } else {
      var iter := new AnotherIter<real,Six>(3.2);  // error (x2): cannot pass in Six as B(0)
    }
  }
}

module FilledInTypeParameters {
  iterator Iter() yields (s: seq)
  {
  }

  codatatype Co = More(Co)
  codatatype GenericCoUnused<G> = More(GenericCoUnused<G>)
  codatatype GenericCo<G> = More(GenericCo<G>, G)
  codatatype NonuniformGenericCo<G> = More(NonuniformGenericCo<int>)
  type Magic = x | 2 <= x < 5 ghost witness 4

  method Test()
  {
    var iter0 := new Iter();
    var m0: seq<Co> := iter0.s;

    var iter1 := new Iter();
    var m1: seq<GenericCoUnused<int>> := iter1.s;

    var iter2 := new Iter();
    var m2: seq<GenericCoUnused<Magic>> := iter2.s;

    var iter3 := new Iter();
    var m3: seq<GenericCo<int>> := iter3.s;

    var iter4 := new Iter();  // error: Auto-init not support for GenericCo<Magic>, as required by the iterator's type parameters
    var m4: seq<GenericCo<Magic>> := iter4.s;

    var iter5 := new Iter();
    var m5: seq<NonuniformGenericCo<int>> := iter5.s;

    var iter6 := new Iter();  // error: Auto-init not support for NonuniformGenericCo<bool>, as required by the iterator's type parameters
    var m6: seq<NonuniformGenericCo<bool>> := iter6.s;
  }
}

module CheckEndOfScopeForDominatingLabels {
  iterator Iter() yields (y: int) {
    label 0:
    yield 500;
    label 1:
    yield 700;
  }
  iterator Iter'() yields (y: int) {
    label 0:  // same label as in Iter; should be fine, of course (but once upon a time wasn't)
    yield 500;
    label 1:
    yield 700;
  }
}

// ---------- initialization of yield parameters -------------------------------

module YieldParameterInitialization {
  trait MaybeEmpty { }
  type GhostAutoInit = x | x % 2 == 1 ghost witness 77
  type CompileAutoInit = x | x % 2 == 1 witness 73

  iterator A() yields (y: MaybeEmpty) {  // error: yield parameter must be of an auto-init type
  }

  iterator B() yields (y: GhostAutoInit) {  // error: yield parameter must be of an auto-init type
  }

  iterator C() yields (y: CompileAutoInit) {
  }

  iterator D() yields (ghost y: MaybeEmpty) {  // error: ghost yield parameter must be of a nonempty type
  }

  iterator E() yields (ghost y: GhostAutoInit) {
  }

  iterator F() yields (ghost y: CompileAutoInit) {
  }
}

// ---------- more constructor tests -------------------------------

module MxConstructors {
  method GenericTester()
  {
    var a: GenericIteratorResult<real> := new GenericIteratorResult; // error: constructor is not mentioned
    var b: GenericIteratorResult<real> := new GenericIteratorResult();
    var c: GenericIterator<int> := new GenericIterator; // error: constructor is not mentioned
    var d: GenericIterator<int> := new GenericIterator(30);
  }

  iterator GenericIterator<T(0)>(t: T) yields (u: T)
  {
    while true {
      yield t;
    }
  }

  iterator GenericIteratorResult<T(0)>() yields (t: T)
  {
    while * {
      yield;
    }
  }
}
