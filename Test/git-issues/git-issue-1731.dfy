// RUN: %dafny /typeSystemRefresh:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module PreviouslyAProblem {
  trait Base {
  }

  class Derived extends Base {
    var n: int
    constructor(n: int)
      ensures this.n == n
    {
      this.n := n;
    }
  }

  function Upcast(d: Derived): Base {
    d
  }

  method Test() {
    var d := new Derived(0);
    var b := Upcast(d);
    if b is Derived {
      var derived := (b as Derived).n;
    }
  }
}

module PreviousRequiredWorkaround {
  trait Base {
  }

  class Derived extends Base {
    var n: int
    constructor(n: int)
      ensures this.n == n
    {
      this.n := n;
    }
  }

  function Upcast(d: Derived): Base {
    d
  }

  method Test() {
    var d := new Derived(0);
    var b: Base := Upcast(d);
    if b is Derived {
      var derived := (b as Derived).n;
    }
  }
}

module SmallerExample {
  trait A0 {}
  trait A1 extends A0 {}
  trait A2 extends A1 {}

  function IsA2(a0: A0): bool {
    if a0 is A1 then
      var a1 := a0 as A1;
      a1 is A2
    else
      true
  }
}

module PreviousRequiredWorkaroundForSmallerExample {
  trait A0 {}
  trait A1 extends A0 {}
  trait A2 extends A1 {}

  function IsA2(a0: A0): bool {
    if a0 is A1 then
      var a1: A1 := a0 as A1;
      a1 is A2
    else
      true
  }
}

module AnotherRepro {
  trait A {}
  trait B extends A {}

  method T(a: A) {
    var aa := a;
    var test: bool := aa is B;
  }

  function F(a: A): bool {
    var aa := a;
    aa is B
  }
}

module OutputExample0 {
  trait A {}
  trait B extends A {}
  trait C extends B {}

  method T(a: A, c: C) {
    if a is B && c is B {
      print "OK!";
    }
  }
}

module OutputExample1 {
  trait A {}
  trait B extends A {}
  trait C extends B {}

  method T(a: A, c: C) {
    var aa := a;
    var cc := c;
    if aa is B && cc is B {
      print "OK!";
    }
  }
}
