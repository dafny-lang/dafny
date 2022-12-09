// RUN: %exits-with 4 %dafny /env:0 /print:"%t.print" /rprint:- "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module OneModule {
  class {:autocontracts} D { }
  class {:autocontracts} C {
    var data: int
    var anotherC: C?
    var dd: D?
    var {:autocontracts false} ee: D?
    var arr: array?<C?>
    predicate Valid()
    {
      0 <= data < 100
    }

    constructor ()
    {
      data := 0;
    }

    method Mutating()
      ensures old(data) <= data
    {
    }

    method Query() returns (d: int)
      ensures d == data
    {
      d := data;
    }

    function F(): nat
    {
      data
    }

    predicate P()
    {
      data < 20
    }

    lemma L()
      ensures data < 100
    {
    }

    twostate lemma TL()
      ensures old(data) <= data  // error: no reason to think this postcondition holds
    {
    }

    method NoBody()
  }
}

module N0 {
  class {:autocontracts} C {
    constructor X()
    constructor Y()
    constructor Z() { }
    method A()
    method B()
    method C() { }
    predicate Valid()
    ghost var Repr: set<object?>
    method {:autocontracts false} K()
      requires Valid() modifies Repr ensures Valid() && fresh(Repr - old(Repr))
    method {:autocontracts false} L()
      requires Valid() modifies Repr ensures Valid() && fresh(Repr - old(Repr))
    method {:autocontracts false} M()
      requires Valid() modifies Repr ensures Valid() && fresh(Repr - old(Repr))
    { }
  }
}
module N1 refines N0 {
  class C ... {
    constructor X...
    constructor Y... { }
    constructor Z... { }
    method A...
    method B... { }
    method C... { }
    method K...
    method L... { }
    method M... { }
  }
}
module N2 refines N1 {
  class C ... {
    constructor X...
    constructor Y... { }
    constructor Z... { }
    method A...
    method B... { }
    method C... { }
    method K...
    method L... { }
    method M... { }
  }
}
