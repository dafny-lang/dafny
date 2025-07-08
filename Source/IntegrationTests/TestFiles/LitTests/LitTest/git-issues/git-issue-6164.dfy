// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Example0 {
  datatype Wrapper = Wrapper(obj: Node)

  class Node {
    var next: Node?
    ghost var wrappers: set<Wrapper>

    function Wrap(): Wrapper {
      Wrapper(this)
    }

    constructor() ensures this.wrappers == {} {
      this.next := null;
      this.wrappers := {};
    }

    constructor Next(next: Node)
      requires next.wrappers == {}
      modifies next`wrappers
      ensures false
    {
      this.wrappers := {};
      next.wrappers := next.wrappers + {Wrapper(next)};
      new;
      assert forall r: Node <- {next} + {} :: this.Wrap() !in r.wrappers;
      assert false; // error
    }
  }

  method Main() {
    var n := new Node();
    var n2 := new Node.Next(n);
    print 1/0;
  }
}

module Example1 {
  datatype Referrer = Referrer(obj: Node, field: int)
  function On(n: Node, f: int): Referrer {
    Referrer(n, f)
  }

  class Node {
    ghost var referrers: set<Referrer>

    var value: int
  }

  class List1 {
    var head: Node?

    ghost var owned: set<Node>

    constructor() {
      head := null;
      owned := {};
    }

    method Add(i: int)
      modifies this
      ensures false
    {
      this.head := new Node;
      this.owned := {head};
      this.head.referrers := this.head.referrers + {On(this.head, 1)};
      assert false; // error
    }
  }
}
