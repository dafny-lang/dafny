// RUN: %dafny /compile:0 /dprint:"%t.dprint" /vcsMaxKeepGoingSplits:10 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Rustan Leino, September 2011.
// This file contains a version of the C5 library's snapshotable trees.  A different verification
// of a version like this has been done by Hannes Mehnert, Filip Sieczkowski, Lars Birkedal, and
// Peter Sestoft in separation logic using Coq.

method Main()
{
  var t := new Tree.Empty();
  ghost var pos := t.Insert(2);
  pos := t.Insert(1);
  pos := t.Insert(3);
  pos := t.Insert(-15);
  pos := t.Insert(0);

  var s := t.CreateSnapshot();
  ghost var sc := s.Contents;
  var it := s.CreateIterator();
  var more := it.MoveNext();
  while (more)
    invariant t.Valid() && !t.IsReadonly && it.Valid();
    invariant more ==> 0 <= it.N < |it.Contents|;
    invariant fresh(t.Repr) && fresh(it.IterRepr) && t.MutableRepr !! it.T.Repr && t.Repr !! it.IterRepr;
    invariant it.T == s && s.Valid() && s.Contents == sc;  // this is not needed in the loop, but serves as an extra test case of the specifications
    decreases |it.Contents| - it.N;
  {
    var x := it.Current();
    print "Main iterates on ", x, "\n";
    pos := t.Insert(x*3);
    more := it.MoveNext();
  }
  assert s.Contents == sc;  // this is not needed in the loop, but serves as an extra test case of the specifications
  t.Print();
}

method TestContents()  // this method tests Tree.Insert's specifications of Contents
{
  var t := new Tree.Empty();          assert t.Contents == [];
  ghost var pos := t.Insert(2);       assert pos == 0 && t.Contents == [2];

  pos := t.Insert(1);
  // Convince the verifier of the absurdity of pos==1
  assert pos == 1 ==> t.Contents == [2,1];
  ghost var hc := [2,1];
  assert hc[0] == 2 && hc[1] == 1 && !Tree.IsSorted(hc);
  // So:
  assert pos == 0 && t.Contents == [1, 2];
}

class Tree
{
  // public
  ghost var Contents: seq<int>;
  var IsReadonly: bool;
  ghost var Repr: set<object>;
  ghost var MutableRepr: set<object>;
  // private
  var root: Node;
  var reprIsShared: bool;

  function Valid(): bool
    reads this, Repr;
  {
    this in MutableRepr && MutableRepr <= Repr && null !in Repr &&
    (root == null ==> Contents == []) &&
    (root != null ==>
      root in Repr && root.Repr <= Repr && this !in root.Repr &&
      root.Valid() && Contents == root.Contents) &&
    IsSorted(Contents) &&
    (IsReadonly ==> reprIsShared) &&
    (!reprIsShared && root != null ==> root.Repr <= MutableRepr) &&
    (reprIsShared ==> MutableRepr == {this})
  }

  static function IsSorted(c: seq<int>): bool  // checks if "c" is sorted and has no duplicates
  {
    forall i, j :: 0 <= i < j < |c| ==> c[i] < c[j]
  }

  constructor Empty()
    modifies this;
    ensures Valid() && Contents == [] && !IsReadonly;
    ensures fresh(Repr - {this});
  {
    Contents := [];
    IsReadonly := false;
    MutableRepr := {this};
    Repr := MutableRepr;
    root := null;
    reprIsShared := false;
  }

  method CreateSnapshot() returns (snapshot: Tree)
    requires Valid();
    modifies Repr;
    ensures Valid() && fresh(Repr - old(Repr));
    ensures Contents == old(Contents) && IsReadonly == old(IsReadonly);
    ensures snapshot != null && snapshot.Valid();
    ensures snapshot.Contents == Contents && snapshot.IsReadonly;
    // the mutable part of the original tree is disjoint from the representation of the snapshot
    ensures snapshot.Repr !! MutableRepr;
    // representation of the snapshot consists of new things of things from the previous tree (that are now immutable)
    ensures fresh(snapshot.Repr - old(Repr));
  {
    // from now on, only "this" is mutable; the rest of the representation is immutable
    Repr := Repr + MutableRepr;
    MutableRepr := {this};
    reprIsShared := true;
    snapshot := new Tree.Private();
    snapshot.Contents := Contents;
    snapshot.IsReadonly := true;
    snapshot.MutableRepr := {snapshot};
    snapshot.Repr := Repr - {this} + {snapshot};
    snapshot.root := root;
    snapshot.reprIsShared := true;
  }

  // private
  constructor Private() { }

  method Insert(x: int) returns (ghost pos: int)
    requires Valid() && !IsReadonly;
    modifies MutableRepr;
    ensures Valid() && fresh(Repr - old(Repr)) && fresh(MutableRepr - old(MutableRepr));
    ensures IsReadonly == old(IsReadonly);
    ensures x in old(Contents) ==> pos < 0 && Contents == old(Contents);
    ensures x !in old(Contents) ==>
      0 <= pos < |Contents| == |old(Contents)| + 1 &&
      Contents == old(Contents[..pos] + [x] + Contents[pos..]);
  {
    if (reprIsShared) {
      root, pos := Node.FunctionalInsert(root, x);
      Contents := root.Contents;
      Repr := root.Repr + {this};
      MutableRepr := {this};
    } else if (root == null) {
      root := new Node.Init(x);
      Contents := root.Contents;
      pos := 0;
      MutableRepr := root.Repr + {this};
      Repr := MutableRepr;
    } else {
      pos := root.MutatingInsert(x);
      Contents := root.Contents;
      MutableRepr := MutableRepr + root.Repr;
      Repr := MutableRepr;
    }
  }

  method CreateIterator() returns (iter: Iterator)
    requires Valid(); // && IsReadonly;
    ensures iter != null && iter.Valid() && fresh(iter.IterRepr);
    ensures iter.T == this && iter.Contents == Contents && iter.N == -1;
  {
    iter := new Iterator.Init(this);
  }

  method Print()
    requires Valid();
    modifies Repr;
    ensures Valid() && fresh(Repr - old(Repr));
    ensures Contents == old(Contents) && IsReadonly == old(IsReadonly);
  {
    print "Tree:";
    var s := CreateSnapshot();
    var it := s.CreateIterator();
    var more := it.MoveNext();
    while (more)
      invariant Valid() && fresh(Repr - old(Repr)) && Contents == old(Contents) && IsReadonly == old(IsReadonly);
      invariant it.Valid();
      invariant more ==> 0 <= it.N < |it.Contents|;
      invariant fresh(it.IterRepr) && MutableRepr !! it.T.Repr && Repr !! it.IterRepr;
      decreases |it.Contents| - it.N;
    {
      var x := it.Current();
      print " ", x;
      more := it.MoveNext();
    }
    print "\n";
  }
}

class Node
{
  ghost var Contents: seq<int>;
  ghost var Repr: set<object>;
  var data: int;
  var left: Node;
  var right: Node;

  function Valid(): bool
    reads this, Repr;
  {
    this in Repr && null !in Repr &&
    (left != null ==>
      left in Repr && left.Repr <= Repr && this !in left.Repr && left.Valid()) &&
    (right != null ==>
      right in Repr && right.Repr <= Repr && this !in right.Repr && right.Valid()) &&
    (left == null && right == null ==> Contents == [data]) &&
    (left != null && right == null ==> Contents == left.Contents + [data]) &&
    (left == null && right != null ==> Contents == [data] + right.Contents) &&
    (left != null && right != null ==> Contents == left.Contents + [data] + right.Contents && left.Repr !! right.Repr) &&
    Tree.IsSorted(Contents)
  }

  constructor Init(x: int)
    modifies this;
    ensures Valid() && fresh(Repr - {this});
    ensures Contents == [x];
  {
    Contents := [x];
    Repr := {this};
    left, data, right := null, x, null;
  }

  constructor Build(left: Node, x: int, right: Node)
    requires this != left && this != right;
    requires left != null ==> left.Valid() && this !in left.Repr &&
               forall e :: e in left.Contents ==> e < x;
    requires right != null ==> right.Valid() && this !in right.Repr &&
               forall e :: e in right.Contents ==> x < e;
    requires left != null && right != null ==> left.Repr !! right.Repr;
    modifies this;
    ensures Valid();
    ensures left == null && right == null ==> Contents == [x] && fresh(Repr - {this});
    ensures left != null && right == null ==> Contents == left.Contents + [x] && fresh(Repr - {this} - left.Repr);
    ensures left == null && right != null ==> Contents == [x] + right.Contents && fresh(Repr - {this} - right.Repr);
    ensures left != null && right != null ==> Contents == left.Contents + [x] + right.Contents && fresh(Repr - {this} - left.Repr - right.Repr);
  {
    Contents := [x];
    Repr := {this};
    this.left, data, this.right := left, x, right;
    if (left != null) {
      Contents := left.Contents + Contents;
      Repr := Repr + left.Repr;
    }
    if (right != null) {
      Contents := Contents + right.Contents;
      Repr := Repr + right.Repr;
    }
  }

  static method FunctionalInsert(n: Node, x: int) returns (r: Node, ghost pos: int)
    requires n != null ==> n.Valid();
    ensures r != null && r.Valid();
    ensures n == null ==> fresh(r.Repr);
    ensures n != null ==> fresh(r.Repr - n.Repr);
    ensures n == null ==> r.Contents == [x] && pos == 0;
    ensures n != null && x in n.Contents ==> r == n && pos < 0;
    ensures n != null && x !in n.Contents ==>
      0 <= pos < |r.Contents| == |n.Contents| + 1 &&
      r.Contents == n.Contents[..pos] + [x] + n.Contents[pos..];
    decreases if n == null then {} else n.Repr;
  {
    if (n == null) {
      r := new Node.Init(x);
      pos := 0;
    } else if (x < n.data) {
      var left;
      assert n.left != null ==> n.data == n.Contents[|n.left.Contents|];
      assert n.left == null ==> n.data == n.Contents[0];
      left, pos := FunctionalInsert(n.left, x);
      // assert n.left == old(n.left);
      if (left == n.left) {
        r, pos := n, -1;
      } else {
        // assert n.left != null ==> forall e :: e in n.left.Contents ==> e < n.data;
        // assert forall e :: e in left.Contents ==> e < n.data;
        r := new Node.Build(left, n.data, n.right);
      }
    } else if (n.data < x) {
      var right;
      assert n.left != null ==> n.data == n.Contents[|n.left.Contents|];
      assert n.left == null ==> n.data == n.Contents[0];
      right, pos := FunctionalInsert(n.right, x);
      if (right == n.right) {
        // assert n != null && x in n.Contents;
        r, pos := n, -1;
      } else {
        // assert n.left != null ==> forall e :: e in n.left.Contents ==> e < n.data;
        // assert forall e :: e in right.Contents ==> n.data < e;
        r := new Node.Build(n.left, n.data, right);
        pos := pos + 1 + if n.left == null then 0 else |n.left.Contents|;
        assert n != null && x !in n.Contents ==> r.Contents == n.Contents[..pos] + [x] + n.Contents[pos..];
      }
    } else {
      r, pos := n, -1;
    }
  }

  method MutatingInsert(x: int) returns (ghost pos: int)
    requires Valid();
    modifies Repr;
    ensures Valid() && fresh(Repr - old(Repr));
    ensures x in old(Contents) ==> pos < 0 && Contents == old(Contents);
    ensures x !in old(Contents) ==>
      0 <= pos < |Contents| == |old(Contents)| + 1 &&
      Contents == old(Contents[..pos] + [x] + Contents[pos..]);
    decreases Repr;
  {
    assert data == Contents[if left==null then 0 else |left.Contents|];
    if (x < data) {
      assert right == null || x !in right.Contents;
      // assert right != null ==> forall e :: e in right.Contents ==> x < e;
      if (left == null) {
        left := new Node.Init(x);
        pos := 0;
      } else {
        // assert forall e :: e in left.Contents ==> e < data;
        pos := left.MutatingInsert(x);
        assert Tree.IsSorted(left.Contents);
        assert right != null ==> Tree.IsSorted(right.Contents);
        // assert forall e :: e in left.Contents ==> e < data;
      }
      Repr := Repr + left.Repr;
      Contents := left.Contents + [data] + if right == null then [] else right.Contents;
      assert Tree.IsSorted(Contents);
    } else if (data < x) {
      assert left == null || x !in left.Contents;
      // assert left != null ==> forall e :: e in left.Contents ==> e < x;
      if (right == null) {
        right := new Node.Init(x);
        pos := 1 + if left == null then 0 else |left.Contents|;
      } else {
        // assert forall e :: e in right.Contents ==> data < e;
        pos := right.MutatingInsert(x);
        assert Tree.IsSorted(right.Contents);
        // assert left != null ==> Tree.IsSorted(left.Contents);
        // assert forall e :: e in right.Contents ==> data < e;
        if (0 <= pos) {
          pos := pos + 1 + if left == null then 0 else |left.Contents|;
          assert (if left == null then [] else left.Contents) + [data] + right.Contents == old(Contents[..pos] + [x] + Contents[pos..]);
        }
      }
      Repr := Repr + right.Repr;
      Contents := (if left == null then [] else left.Contents) + [data] + right.Contents;
      assert Tree.IsSorted(Contents);
    } else {
      pos := -1;
    }
  }
}

class Iterator
{
  // public
  ghost var IterRepr: set<object>;  // note, IterRepr does not include T.Repr
  ghost var Contents: seq<int>;
  ghost var N: int;
  var T: Tree;
  // private
  var initialized: bool;
  var stack: List;

  function Valid(): bool
    reads this, IterRepr, T;
    reads if T != null then T.Repr else {};
  {
    this in IterRepr && null !in IterRepr &&
    T != null && T.Valid() && IterRepr !! T.Repr &&
    Contents == T.Contents && -1 <= N <= |Contents| &&
    (initialized <==> 0 <= N) &&
    (N < 0 ==> R(stack, 0, Contents, T.Repr)) &&
    (0 <= N ==> R(stack, N, Contents, T.Repr))
  }

  // R(wlist, n, C, Nodes) says that C[n..] are data items yet to be processed.
  // In more detail, wlist is a stack of tree fragments, where the concatenation of the
  // "load" of each tree fragment (from the top of the stack downwards) equals
  // C[n..].  A tree fragment is either
  //  * for Nil, the empty fragment
  //  * for Cons(p, rest), fragment [p.data]+p.right.Contents
  // In each case, R(wlist,n,C,Nodes) implies that the fragment wlist proper is a prefix of C[n..].
  // Nodes is (an overapproximation of) the set of nodes read by R.
  static function R(wlist: List, n: int, C: seq<int>, Nodes: set<object>): bool
    reads Nodes;
    decreases wlist;
  {
    match wlist
    case Nil => n == |C|
    case Cons(p, rest) =>
      p != null && p in Nodes && p.Repr <= Nodes && p.Valid() &&
      0 <= n < |C| && p.data == C[n] &&
      R(rest, n + 1 + if p.right==null then 0 else |p.right.Contents|, C, Nodes) &&
      p.Contents[if p.left==null then 0 else |p.left.Contents| ..] <= C[n..]
  }

  constructor Init(t: Tree)
    requires t != null && t.Valid() && this !in t.Repr;
    modifies this;
    ensures Valid() && fresh(IterRepr - {this});
    ensures T == t && Contents == t.Contents && N == -1;
  {
    T := t;
    IterRepr := {this};
    Contents := T.Contents;
    initialized, stack, N := false, Nil, -1;
    if (t.root != null) {
      stack := Push(stack, 0, t.root, Contents, T.Repr);
    }
  }

  // private
  static method Push(stIn: List, ghost n: int, p: Node, ghost C: seq<int>, ghost Nodes: set<object>) returns (st: List)
    requires p != null && p in Nodes && p.Repr <= Nodes && p.Valid();
    requires 0 <= n <= |C|;
    requires p.Contents <= C[n..];
    requires R(stIn, n + |p.Contents|, C, Nodes);
    ensures R(st, n, C, Nodes);
    decreases p.Contents;
  {
    st := Cons(p, stIn);

    assert p.data == p.Contents[if p.left == null then 0 else |p.left.Contents|];  // lemma
    if (p.left != null) {
      st := Push(st, n, p.left, C, Nodes);
    }
  }

  method Current() returns (x: int)
    requires Valid() && 0 <= N < |Contents|;
    ensures x == Contents[N];
  {
    match (stack) {
      case Cons(y, rest) => x := y.data;
    }
  }

  method MoveNext() returns (hasCurrent: bool)
    requires Valid() && N <= |Contents|;
    modifies IterRepr;
    ensures Valid() && fresh(IterRepr - old(IterRepr)) && T.Repr == old(T.Repr);
    ensures Contents == old(Contents) && T == old(T);
    ensures old(N) < |Contents| ==> N == old(N) + 1;
    ensures old(N) == |Contents| ==> N == old(N);
    ensures hasCurrent <==> 0 <= N < |Contents|;
  {
    if (!initialized) {
      initialized, N := true, 0;
      hasCurrent := stack != Nil;
    } else {
      match (stack) {
        case Nil =>
          hasCurrent := false;
        case Cons(p, rest) =>
          // lemmas:
          assert R(rest, N + 1 + if p.right==null then 0 else |p.right.Contents|, Contents, T.Repr);
          ghost var k := if p.left==null then 0 else |p.left.Contents|;
          assert p.Contents[k..] == [p.data] + p.Contents[k+1..];
          assert p.Contents[k+1..] <= Contents[N+1..];

          stack, N := rest, N+1;

          if (p.right != null) {
            stack := Push(stack, N, p.right, Contents, T.Repr);
          }
          hasCurrent := stack != Nil;
      }
    }
    match (stack) { case Nil => assert N == |Contents|; case Cons(p, rest) => assert N < |Contents|; } // lemma
  }
}

datatype List = Nil | Cons(Node, List);

/*  The following method shows the problem of concurrent modifications and shows that the
 *  design of the snapshotable trees herein handle this correctly.  That is, after inserting
 *  into a tree that is being iterated, use of the associated iterator can no longer be
 *  proved to be correct.
 *
method TestConcurrentModification(t: Tree)
  requires t != null && t.Valid() && !t.IsReadonly;
  modifies t.MutableRepr;
{
  var it := t.CreateIterator();
  var more := it.MoveNext();
  if (more) {
    var pos := t.Insert(52);  // this modification of the collection renders all associated iterators invalid
    more := it.MoveNext();  // error: operation t.Insert may have made this iterator invalid
  }
}
*/
