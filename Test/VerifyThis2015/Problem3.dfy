// RUN: %dafny /compile:3 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Rustan Leino
// 12 April 2015
// VerifyThis 2015
// Problem 3 -- Dancing Links


// The following method demonstrates that Remove and PutBack (defined below) have the desired properties
method Test(dd: DoublyLinkedList, x: Node)
  requires dd.Valid()
  requires x in dd.Nodes && x != dd.Nodes[0] && x != dd.Nodes[|dd.Nodes|-1]
  modifies dd, dd.Nodes
  ensures dd.Valid() && dd.Nodes == old(dd.Nodes)
{
  ghost var k := dd.Remove(x);
  dd.PutBack(x, k);
}
// It is also possible to remove and put back any number of elements, provided these operations are
// done in a FOLI order.
method TestMany(dd: DoublyLinkedList, xs: seq<Node>)
  requires dd.Valid()
  requires forall x :: x in xs ==> x in dd.Nodes && x != dd.Nodes[0] && x != dd.Nodes[|dd.Nodes|-1]
  requires forall i,j :: 0 <= i < j < |xs| ==> xs[i] != xs[j]
  modifies dd, dd.Nodes
  ensures dd.Valid() && dd.Nodes == old(dd.Nodes)
{
  if xs != [] {
    var x := xs[0];
    ghost var k := dd.Remove(x);
    forall y | y in xs[1..]
      ensures y in dd.Nodes && y != dd.Nodes[0] && y != dd.Nodes[|dd.Nodes|-1]
    {
      assert forall z :: z in old(dd.Nodes) ==> z in dd.Nodes || z == x;
      assert x == old(dd.Nodes)[k];
    }
    TestMany(dd, xs[1..]);
    dd.PutBack(x, k);
  }
}

// And here's a Main program that shows that doubly linked lists do exist (well, at least there is one :))
method Main()
{
  var a0 := new Node;
  var a1 := new Node;
  var a2 := new Node;
  var a3 := new Node;
  var a4 := new Node;
  var a5 := new Node;
  var dd := new DoublyLinkedList([a0, a1, a2, a3, a4, a5]);
  Test(dd, a3);
  TestMany(dd, [a2, a4, a3]);
}

class Node {
  var L: Node?
  var R: Node?
}

class DoublyLinkedList {
  ghost var Nodes: seq<Node>  // sequence of nodes in the linked list
  // Valid() says that the data structure is a proper doubly linked list
  ghost predicate Valid()
    reads this, Nodes
  {
    (|Nodes| > 0 ==>
      Nodes[0].L == null && (forall i {:trigger Nodes[i].L} :: 1 <= i < |Nodes| ==> Nodes[i].L == Nodes[i-1]) &&
      (forall i {:trigger Nodes[i].R} :: 0 <= i < |Nodes|-1 ==> Nodes[i].R == Nodes[i+1]) && Nodes[|Nodes|-1].R == null
    ) &&
    forall i,j :: 0 <= i < j < |Nodes| ==> Nodes[i] != Nodes[j]  // this is actually a consequence of the previous conditions
  }
  // This constructor just shows that there is a way to create a doubly linked list.  It accepts
  // as an argument the sequences of Nodes to construct the doubly linked list from.  The constructor
  // will change all the .L and .R pointers of the given nodes in order to create a properly
  // formed list.
  constructor (nodes: seq<Node>)
    requires forall i,j :: 0 <= i < j < |nodes| ==> nodes[i] != nodes[j]
    modifies nodes
    ensures Valid() && Nodes == nodes
  {
    if nodes != [] {
      var prev, n := nodes[0], 1;
      prev.L, prev.R := null, null;
      while n < |nodes|
        invariant 1 <= n <= |nodes|
        invariant nodes[0].L == null
        invariant prev == nodes[n-1] && prev.R == null
        invariant forall i :: 1 <= i < n ==> nodes[i].L == nodes[i-1]
        invariant forall i :: 0 <= i < n-1 ==> nodes[i].R == nodes[i+1]
      {
        nodes[n].L, prev.R, prev := prev, nodes[n], nodes[n];
        prev.R := null;
        n := n + 1;
      }
    }
    Nodes := nodes;
  }

  ghost function PopMiddle<T>(s: seq<T>, k: nat) : seq<T>
    requires k < |s| {
      s[..k] + s[k+1..]
  }

  ghost predicate Injective<T>(s: seq<T>) {
    forall j, k :: 0 <= j < k < |s| ==> s[j] != s[k]
  }

  lemma InjectiveAfterPop<T>(s: seq<T>, k: nat)
    requires k < |s|
    requires Injective(s)
    ensures  Injective(PopMiddle(s, k))
  {
  }

  method Remove(x: Node) returns (ghost k: int)
    requires Valid()
    requires x in Nodes && x != Nodes[0] && x != Nodes[|Nodes|-1]  // not allowed to remove end nodes; you may think of them as a sentinel nodes
    modifies this, Nodes
    ensures Valid()
    ensures 0 <= k < |old(Nodes)| && x == old(Nodes)[k]
    ensures Nodes == old(Nodes)[..k] + old(Nodes)[k+1..] && x.L == old(x.L) && x.R == old(x.R)
  {
    k :| 1 <= k < |Nodes|-1 && Nodes[k] == x;
    x.R.L := x.L;
    x.L.R := x.R;

    Nodes := Nodes[..k] + Nodes[k+1..];
    assert |Nodes| > 0;
  }

  // One might consider have a precondition that says there exists a "k" with the properties given here.
  // However, we want to be able to refer to "k" in the postcondition as well, so it's convenient to
  // burden the client with having to pass in "k" as a ghost parameter.  This, however, is really no
  // extra burden on the client, because if the client would have been able to show the existence of
  // such a "k", then the client can easily just use an assign-such-that statement to obtain such a
  // value "k".
  method PutBack(x: Node, ghost k: int)
    requires Valid()
    requires 1 <= k < |Nodes| && x.L == Nodes[k-1] && x.R == Nodes[k]
    modifies this, Nodes, x
    ensures Valid()
    ensures Nodes == old(Nodes)[..k] + [x] + old(Nodes)[k..]
  {
    x.R.L := x;
    x.L.R := x;
    Nodes := Nodes[..k] + [x] + Nodes[k..];
  }
}

// --------------------------------------------------------
// If it were not required to build a data structure (like the class above) that supports the
// Remove and PutBack operations, the operations can easily be verified to compose into the
// identity transformation.  The following method shows that the two operations, under a suitable
// precondition, have no net effect on any .L or .R field.

method Alt(x: Node)
  requires x.L != null && x.R != null
  requires x.L.R == x && x.R.L == x  // links are mirrored
  modifies x, x.L, x.R
  ensures forall y: Node :: old(allocated(y)) ==> y.L == old(y.L) && y.R == old(y.R)
{
  // remove
  x.R.L := x.L;
  x.L.R := x.R;
  // put back
  x.R.L := x;
  x.L.R := x;
}
