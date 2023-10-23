// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class IntSet {
  ghost var Contents: set<int>
  ghost var Repr: set<object>

  var root: Node?

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    this in Repr &&
    (root == null ==> Contents == {}) &&
    (root != null ==>
       root in Repr && root.Repr <= Repr && this !in root.Repr &&
       root.Valid() &&
       Contents == root.Contents)
  }

  constructor Init()
    ensures Valid() && fresh(Repr)
    ensures Contents == {}
  {
    root := null;
    Repr := {this};
    Contents := {};
  }

  function Find(x: int): bool
    requires Valid()
    reads Repr
    ensures Find(x) <==> x in Contents
  {
    root != null && root.Find(x)
  }

  method Insert(x: int)
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures Contents == old(Contents) + {x}
  {
    var t := InsertHelper(x, root);
    root := t;
    Contents := root.Contents;
    Repr := root.Repr + {this};
  }

  static method InsertHelper(x: int, n: Node?) returns (m: Node)
    requires n == null || n.Valid()
    modifies if n != null then n.Repr else {}
    ensures m.Valid()
    ensures n == null ==> fresh(m.Repr) && m.Contents == {x}
    ensures n != null ==> m == n && n.Contents == old(n.Contents) + {x}
    ensures n != null ==> fresh(n.Repr - old(n.Repr))
    decreases if n == null then {} else n.Repr
  {
    if n == null {
      m := new Node.Init(x);
    } else if x == n.data {
      m := n;
    } else {
      if x < n.data {
        assert n.right == null || n.right.Valid();
        var t := InsertHelper(x, n.left);
        n.left := t;
        n.Repr := n.Repr + n.left.Repr;
      } else {
        assert n.left == null || n.left.Valid();
        var t := InsertHelper(x, n.right);
        n.right := t;
        n.Repr := n.Repr + n.right.Repr;
      }
      n.Contents := n.Contents + {x};
      m := n;
    }
  }

  method Remove(x: int)
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures Contents == old(Contents) - {x}
  {
    if root != null {
      var newRoot := root.Remove(x);
      root := newRoot;
      if root == null {
        Contents := {};
        Repr := {this};
      } else {
        Contents := root.Contents;
        Repr := root.Repr + {this};
      }
    }
  }
}

class Node {
  ghost var Contents: set<int>
  ghost var Repr: set<object>

  var data: int
  var left: Node?
  var right: Node?

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    this in Repr &&
    (left != null ==>
      left in Repr &&
      left.Repr <= Repr && this !in left.Repr &&
      left.Valid() &&
      (forall y :: y in left.Contents ==> y < data)) &&
    (right != null ==>
      right in Repr &&
      right.Repr <= Repr && this !in right.Repr &&
      right.Valid() &&
      (forall y :: y in right.Contents ==> data < y)) &&
    (left == null && right == null ==>
      Contents == {data}) &&
    (left != null && right == null ==>
      Contents == left.Contents + {data}) &&
    (left == null && right != null ==>
      Contents == {data} + right.Contents) &&
    (left != null && right != null ==>
      left.Repr !! right.Repr &&
      Contents == left.Contents + {data} + right.Contents)
  }

  constructor Init(x: int)
    ensures Valid() && fresh(Repr)
    ensures Contents == {x}
  {
    data := x;
    left := null;
    right := null;
    Contents := {x};
    Repr := {this};
  }

  function Find(x: int): bool
    requires Valid()
    reads Repr
    ensures Find(x) <==> x in Contents
    decreases Repr
  {
    if x == data then
      true
    else if left != null && x < data then
      left.Find(x)
    else if right != null && data < x then
      right.Find(x)
    else
      false
  }

  method Remove(x: int) returns (node: Node?)
    requires Valid()
    modifies Repr
    ensures fresh(Repr - old(Repr))
    ensures node != null ==> node.Valid()
    ensures node == null ==> old(Contents) <= {x}
    ensures node != null ==> node.Repr <= Repr && node.Contents == old(Contents) - {x}
    decreases Repr
  {
    node := this;
    if left != null && x < data {
      var t := left.Remove(x);
      left := t;
      Contents := Contents - {x};
      if left != null { Repr := Repr + left.Repr; }
    } else if right != null && data < x {
      var t := right.Remove(x);
      right := t;
      Contents := Contents - {x};
      if right != null { Repr := Repr + right.Repr; }
    } else if x == data {
      if left == null && right == null {
        node := null;
      } else if left == null {
        node := right;
      } else if right == null {
        node := left;
      } else {
        // rotate
        var min, r := right.RemoveMin();
        data := min;  right := r;
        Contents := Contents - {x};
        if right != null { Repr := Repr + right.Repr; }
      }
    }
  }

  method RemoveMin() returns (min: int, node: Node?)
    requires Valid()
    modifies Repr
    ensures fresh(Repr - old(Repr))
    ensures node != null ==> node.Valid()
    ensures node == null ==> old(Contents) == {min}
    ensures node != null ==> node.Repr <= Repr && node.Contents == old(Contents) - {min}
    ensures min in old(Contents) && (forall x :: x in old(Contents) ==> min <= x)
    decreases Repr
  {
    if left == null {
      min := data;
      node := right;
    } else {
      var t;
      min, t := left.RemoveMin();
      left := t;
      node := this;
      Contents := Contents - {min};
      if left != null { Repr := Repr + left.Repr; }
    }
  }
}

class Main {
  method Client0(x: int)
  {
    var s := new IntSet.Init();

    s.Insert(12);
    s.Insert(24);
    var present := s.Find(x);
    assert present <==> x == 12 || x == 24;
  }

  method Client1(s: IntSet, x: int)
    requires s.Valid()
    modifies s.Repr
  {
    s.Insert(x);
    s.Insert(24);
    assert old(s.Contents) - {x,24} == s.Contents - {x,24};
  }
}
