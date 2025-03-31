// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait Tr<X> extends object { }

class A extends Tr<int> { }
class B extends Tr<real> { }
class C<Y> extends Tr<Y> { }

method M(a: A, b: B) {
  var c: C? := *;
  var t;  // Tr?<int>
  t := a;
  t := c;
}

method N(a: A, b: B) {
  var c: C?<int> := *;
  var t: Tr<int>;
  t := a;
  t := c;  // error: c may be null
}

method Q(a: A?) returns (t: Tr<int>) {
  t := a;  // error: a may be null
}

method P(a: A?) {
  var t: A;
  t := a;  // error: a may be null
}

method R(a: A) {
  var t: A?;
  t := a;
}

module ForallSubstitution {
  trait Tr<X> {
    ghost predicate P<Y>(x: X, y: Y) { true }
    lemma Lemma<Y>(x: X, y: Y)
      ensures P(x, y)
    {
    }
  }
  class Cl extends Tr<int> {
  }

  lemma Caller(c: Cl) {
    forall a: int, b: real {
      // test that the appropriate type substitutions happen on the next line
      c.Lemma(a, b);
    }
  }
}

module ReceiverResolution {
  trait MyTrait<U> {
    ghost const Repr: set<object>
    ghost function F(): set<object> {{}}
  }

  class MyClass<T, R> extends MyTrait<T> {
    constructor() {
    }
  }

  method M() {
    var foo := new MyClass<int, int>();
    // By the time the type inference looks at .Repr in the following line, the only thing
    // that has been definitely decided about the type of "foo" is that it is some subtype
    // of MyTrait. This test tries to check that the Dafny implementation doesn't hang on
    // to the type parameters of that MyTrait, but instead uses the type parameters of
    // the eventually inferred type of "foo", MyClass<int, int>. This was once buggy.
    ghost var r := foo.Repr;
  }

  method N() {
    var foo := new MyClass<int, int>();
    ghost var f := foo.F();
  }
}
