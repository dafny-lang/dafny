// RUN: %dafny /verifyAllModules /allocated:1 /compile:3 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var c, d := new A, new A;
  L(c, d);  // error: 'c' is not old
}

twostate lemma L(c: A, new d: A)
  requires allocated(c) && allocated(d)
{
  var x := old(c.f);
  var y := old(d.f);  // error: trying to use new 'd' in previous state
}

class A {
  var f: int
  var g: A?

  function GimmieF(): int
    reads this
  {
    f
  }

  twostate lemma L1(other: A) returns (res: bool)
    requires unchanged(this)
    ensures res ==> this == other
  {
    res := this == other;
  }

  twostate lemma L2(a: A, b: A)
    requires old(a != b)
  {}

  twostate lemma L3(a: A, new b: A)
    requires allocated(a) && allocated(b)
    requires old(a.f != b.f)  // error: b might not exist in the old state
  {}

  twostate lemma L3_and_a_half(a: A, new b: A)
    requires allocated(a) && allocated(b)
    requires old(a.GimmieF() == b.GimmieF())  // error: b might not exist in old state
  {}

  twostate lemma L4(new a: A)
    requires old(allocated(a))
    requires unchanged(a)
  {
    assert a.f == old(a.f);
    assert a.GimmieF() == old(a.GimmieF());  // we get that everything about a, including its allocatedness,
                                             // is the same in the previous and current states
  }

  method M4()
  {
    var a := new A;
    if * {
      assert a.f == old(a.f);  // error: a was not allocated initial state
    } else {
      assert a.GimmieF() == old(a.GimmieF());  // error: a was not allocated initial state
    }
  }

  twostate lemma L5(new a: A, new b: A)
  {}

  twostate lemma L6(a: A)
    requires unchanged(a)
  {
    assert a.f == old(a.f);
    assert a.GimmieF() == old(a.GimmieF());
  }

  twostate lemma L7(a: A)
  {
    assert a.f == old(a.f);  // error: state need not agree on a.f
  }
}

class Node {
  var x: int
  var next: Node?
  ghost var Repr: set<Node>
  predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    this in Repr && (forall o :: o in Repr ==> allocated(o)) &&
    (next != null ==> next in Repr && next.Repr <= Repr && this !in next.Repr && next.Valid())
  }
  constructor (y: int)
    ensures Valid() && fresh(Repr)
  {
    x, next := y, null;
    Repr := {this};
  }
  constructor Prepend(y: int, nxt: Node)
    requires nxt.Valid()
    ensures Valid() && fresh(Repr - nxt.Repr)
  {
    x, next := y, nxt;
    Repr := {this} + nxt.Repr;
  }

  function method Sum(): int
    requires Valid()
    reads Repr
  {
    if next == null then x else x + next.Sum()
  }

  method M(node: Node)
    requires Valid()
    modifies node
    ensures Valid()
  {
    var s := Sum();
    node.x := node.x + 1;
    M_Lemma(node);
    assert s <= Sum();
  }

  twostate lemma M_Lemma(node: Node)
    requires old(Valid()) && old(allocated(Repr))
    requires old(node.x) <= node.x && old((node.next, node.Repr)) == (node.next, node.Repr)
    requires unchanged(old(Repr) - {node})
    ensures Valid() && old(Sum()) <= Sum()
    decreases Repr
  {
    if next != null {
      next.M_Lemma(node);
    }
  }

  static twostate lemma M_Lemma_Static(self: Node, node: Node)
    requires old(self.Valid())
    requires old(node.x) <= node.x && old((node.next, node.Repr)) == (node.next, node.Repr)
    requires unchanged(old(self.Repr) - {node})
    ensures self.Valid() && old(self.Sum()) <= self.Sum()
    decreases self.Repr
  {
    if self.next != null {
      M_Lemma_Static(self.next, node);
    }
  }

  static twostate lemma M_Lemma_Forall(self: Node, node: Node)
    requires old(self.Valid())
    requires old(node.x) <= node.x && old((node.next, node.Repr)) == (node.next, node.Repr)
    requires unchanged(old(self.Repr) - {node})
    ensures self.Valid() && old(self.Sum()) <= self.Sum()
    decreases self.Repr
  {
    forall n: Node | old(allocated(n)) && old(n.Repr < self.Repr && n.Valid())
      ensures n.Valid() && old(n.Sum()) <= n.Sum()
    {
      M_Lemma_Forall(n, node);
    }
    var n := self.next;
    if n != null {
      assert old(allocated(n)) && old(n.Repr < self.Repr && n.Valid());
      assert n.Valid() && old(n.Sum()) <= n.Sum();
    }
  }

  twostate lemma M_Lemma_Alt(node: Node)
    requires old(Valid())
    requires old(node.x) <= node.x && old((node.next, node.Repr)) == (node.next, node.Repr)
    requires forall n :: n in old(Repr) && n != node ==> n.x == old(n.x) && n.next == old(n.next) && n.Repr == old(n.Repr)
    ensures Valid() && old(Sum()) <= Sum()
    decreases Repr
  {
    if next != null {
      next.M_Lemma_Alt(node);
    }
  }

  static twostate lemma M_Lemma_Alt_Static(self: Node, node: Node)
    requires old(self.Valid())
    requires old(node.x) <= node.x && old((node.next, node.Repr)) == (node.next, node.Repr)
    requires forall n :: n in old(self.Repr) && n != node ==> n.x == old(n.x) && n.next == old(n.next) && n.Repr == old(n.Repr)
    ensures self.Valid() && old(self.Sum()) <= self.Sum()
    decreases self.Repr
  {
    if self.next != null {
      M_Lemma_Alt_Static(self.next, node);
    }
  }
}

class {:autocontracts} NodeAuto {
  var x: int
  var next: NodeAuto?
  constructor (y: int)
  {
    x, next := y, null;
  }
  constructor {:autocontracts false} Prepend(y: int, nxt: NodeAuto)
    requires nxt.Valid() && allocated(nxt.Repr);
    ensures Valid() && fresh(Repr - nxt.Repr)
  {
    x, next := y, nxt;
    Repr := {this} + nxt.Repr;
  }

  function method Sum(): int
  {
    if next == null then x else x + next.Sum()
  }

  method M(node: NodeAuto)
    requires allocated(Repr)
    modifies node
  {
    var s := Sum();
    node.x := node.x + 1;
    M_Lemma(node);
    assert s <= Sum();
  }

  twostate lemma M_Lemma(node: NodeAuto)
    requires old(node.x) <= node.x && old((node.next, node.Repr)) == (node.next, node.Repr)
    requires old(allocated(Repr)) && unchanged(old(Repr) - {node})
    ensures Valid() && old(Sum()) <= Sum()
    decreases Repr
  {
    if next != null {
      next.M_Lemma(node);
    }
  }

  twostate lemma M_Lemma_Alt(node: NodeAuto)
    requires old(node.x) <= node.x && old((node.next, node.Repr)) == (node.next, node.Repr)
    requires forall n: NodeAuto :: n in old(Repr) && n != node ==> n.x == old(n.x) && n.next == old(n.next) && n.Repr == old(n.Repr)
    ensures Valid() && old(Sum()) <= Sum()
    decreases Repr
  {
    if next != null {
      next.M_Lemma_Alt(node);
    }
  }
}
