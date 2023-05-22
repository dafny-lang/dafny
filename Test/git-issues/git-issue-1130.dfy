// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var a := new Issue.Foo<int>();
  Issue.CallUseFoo(a);

  var b := new Variation.Foo<int>();
  Variation.CallUseFoo(b);

  var c := new AnotherVariation.Foo<int>();
  AnotherVariation.CallUseFoo(c);

  print "\n";
}

module Issue
{
  class Foo<T> {
    ghost function Repr(): set<object> { {this} }
    constructor() {}
  }

  method UseFoo<T>(t: Foo<T>)
    modifies t.Repr()
  {
    print 0;
  }

  method CallUseFoo<T>(t: Foo<T>)
    modifies t.Repr()
  {
    // the following line once produced malformed Boogie
    UseFoo(t);
  }
}

// the following variation was working all along
module Variation {
  class Foo<T> {
    ghost function Repr(): set<object> { {this} }
    constructor() {}
  }

  class UseFooHelper<T>
  {
    const foo: Foo<T>
    constructor(foo: Foo<T>)
      ensures this.foo == foo
    {
      this.foo := foo;
    }

    method Do()
      modifies foo.Repr()
    {
      print 1;
    }
  }

  method CallUseFoo<T>(t: Foo<T>)
    modifies t.Repr()
  {
    var fh := new UseFooHelper(t);
    fh.Do();
  }
}

// the following variation was also working all along
module AnotherVariation
{
  class Foo<T> {
    ghost function Repr(): set<object> { {this} }
    constructor() {}

    method UseFoo()
      modifies Repr()
    {
      print 2;
    }
  }

  method CallUseFoo<T>(t: Foo<T>)
    modifies t.Repr()
  {
    t.UseFoo();
  }
}
