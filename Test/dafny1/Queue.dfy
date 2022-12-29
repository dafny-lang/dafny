// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Queue.dfy
// Dafny version of Queue.bpl
// Rustan Leino, 2008

class Queue<T(0)> {
  var head: Node<T>
  var tail: Node<T>

  ghost var contents: seq<T>
  ghost var footprint: set<object>
  ghost var spine: set<Node<T>>

  predicate Valid()
    reads this, footprint
  {
    this in footprint && spine <= footprint &&
    head in spine &&
    tail in spine &&
    tail.next == null &&
    (forall n ::
      n in spine ==>
        n.footprint <= footprint && this !in n.footprint &&
        n.Valid() &&
        (n.next == null ==> n == tail)) &&
    (forall n ::
      n in spine ==>
        n.next != null ==> n.next in spine) &&
    contents == head.tailContents
  }

  constructor Init()
    ensures Valid() && fresh(footprint - {this})
    ensures |contents| == 0
  {
    var n: Node<T> := new Node<T>.Init();
    head := n;
    tail := n;
    contents := n.tailContents;
    footprint := {this} + n.footprint;
    spine := {n};
  }

  method Rotate()
    requires Valid()
    requires 0 < |contents|
    modifies footprint
    ensures Valid() && fresh(footprint - old(footprint))
    ensures contents == old(contents)[1..] + old(contents)[..1]
  {
    var t := Front();
    Dequeue();
    Enqueue(t);
  }

  method RotateAny()
    requires Valid()
    requires 0 < |contents|
    modifies footprint
    ensures Valid() && fresh(footprint - old(footprint))
    ensures |contents| == |old(contents)|
    ensures exists i :: 0 <= i && i <= |contents| &&
              contents == old(contents)[i..] + old(contents)[..i]
  {
    var t := Front();
    Dequeue();
    Enqueue(t);
  }

  method IsEmpty() returns (isEmpty: bool)
    requires Valid()
    ensures isEmpty <==> |contents| == 0
  {
    isEmpty := head == tail;
  }

  method Enqueue(t: T)
    requires Valid()
    modifies footprint
    ensures Valid() && fresh(footprint - old(footprint))
    ensures contents == old(contents) + [t]
  {
    var n := new Node<T>.Init();
    n.data := t;
    tail.next := n;
    tail := n;

    forall m | m in spine {
      m.tailContents := m.tailContents + [t];
    }
    contents := head.tailContents;

    forall m | m in spine {
      m.footprint := m.footprint + n.footprint;
    }
    footprint := footprint + n.footprint;

    spine := spine + {n};
  }

  method Front() returns (t: T)
    requires Valid()
    requires 0 < |contents|
    ensures t == contents[0]
  {
    t := head.next.data;
  }

  method Dequeue()
    requires Valid()
    requires 0 < |contents|
    modifies footprint
    ensures Valid() && fresh(footprint - old(footprint))
    ensures contents == old(contents)[1..]
  {
    var n := head.next;
    head := n;
    contents := n.tailContents;
  }
}

class Node<T(0)> {
  var data: T
  var next: Node?<T>

  ghost var tailContents: seq<T>
  ghost var footprint: set<object>

  predicate Valid()
    reads this, footprint
  {
    this in footprint &&
    (next != null ==> next in footprint && next.footprint <= footprint) &&
    (next == null ==> tailContents == []) &&
    (next != null ==> tailContents == [next.data] + next.tailContents)
  }

  constructor Init()
    ensures Valid() && fresh(footprint - {this})
    ensures next == null
  {
    next := null;
    tailContents := [];
    footprint := {this};
  }
}

class Main<U(0)> {
  method A<T(0)>(t: T, u: T, v: T)
  {
    var q0 := new Queue<T>.Init();
    var q1 := new Queue<T>.Init();

    q0.Enqueue(t);
    q0.Enqueue(u);

    q1.Enqueue(v);

    assert |q0.contents| == 2;

    var w := q0.Front();
    assert w == t;
    q0.Dequeue();

    w := q0.Front();
    assert w == u;

    assert |q0.contents| == 1;
    assert |q1.contents| == 1;
  }

  method Main2(t: U, u: U, v: U, q0: Queue<U>, q1: Queue<U>)
    requires q0.Valid()
    requires q1.Valid()
    requires q0.footprint !! q1.footprint
    requires |q0.contents| == 0
    modifies q0.footprint, q1.footprint
    ensures fresh(q0.footprint - old(q0.footprint))
    ensures fresh(q1.footprint - old(q1.footprint))
  {
    q0.Enqueue(t);
    q0.Enqueue(u);

    q1.Enqueue(v);

    assert |q0.contents| == 2;

    var w := q0.Front();
    assert w == t;
    q0.Dequeue();

    w := q0.Front();
    assert w == u;

    assert |q0.contents| == 1;
    assert |q1.contents| == old(|q1.contents|) + 1;
  }
}
