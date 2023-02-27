// RUN: %exits-with 4 %dafny /compile:3 /proverOpt:O:smt.qi.eager_threshold=80 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Rustan Leino, September 2011.
// This file contains a version of the C5 library's snapshotable trees.  A different verification
// of a version like this has been done by Hannes Mehnert, Filip Sieczkowski, Lars Birkedal, and
// Peter Sestoft in separation logic using Coq.

module SnapTreeTestHarness {
  import opened SnapTree

  method Main()
  {
    var t := new SnapTree.Tree.Empty();
    ghost var pos := t.Insert(2);
    pos := t.Insert(1);
    pos := t.Insert(3);
    pos := t.Insert(-15);
    pos := t.Insert(0);

    var s := t.CreateSnapshot();
    ghost var sc := s.Contents;
    var it := s.CreateIterator();
    var more := it.MoveNext();
    while more
      invariant t.Valid() && !t.IsReadonly && it.Valid()
      invariant more ==> 0 <= it.N < |it.Contents|
      invariant fresh(t.Repr) && fresh(it.IterRepr)
      invariant t.MutableRepr <= t.Repr && it !in t.MutableRepr && t.MutableRepr !! it.T.Repr && t.Repr !! it.IterRepr
      invariant it.T == s && s.Valid()
      invariant s.Contents == sc  // this is not needed in the loop, but serves as an extra test case of the specifications
      decreases |it.Contents| - it.N
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
    var t := new SnapTree.Tree.Empty();   assert t.Contents == [];
    ghost var pos := t.Insert(2);         assert pos == 0 && t.Contents == [2];

    pos := t.Insert(1);
    // Convince the verifier of the absurdity of pos==1
    assert pos == 1 ==> t.Contents == [2,1];
    ghost var hc := [2,1];
    SnapTree.Tree.IsSortedProperty(hc);
    assert hc[0] == 2 && hc[1] == 1 && !SnapTree.Tree.IsSorted(hc);
    // So:
    assert pos == 0 && t.Contents == [1, 2];
  }

  /*  The following method shows the problem of concurrent modifications and shows that the
   *  design of the snapshotable trees herein handle this correctly.  That is, after inserting
   *  into a tree that is being iterated, use of the associated iterator can no longer be
   *  proved to be correct.
   */
  method TestConcurrentModification(t: SnapTree.Tree)
    requires t.Valid() && !t.IsReadonly
    modifies t.MutableRepr
  {
    var it := t.CreateIterator();
    var more := it.MoveNext();
    if more {
      var pos := t.Insert(52);  // this modification of the collection renders all associated iterators invalid
      more := it.MoveNext();  // error: operation t.Insert may have made this iterator invalid
    }
  }
}

// ------------------------------------------------------------------------

module SnapTree {

  datatype List = Nil | Cons(Node, List)

  class Tree
  {
    // public
    ghost var Contents: seq<int>
    var IsReadonly: bool
    ghost var Repr: set<object>
    ghost var MutableRepr: set<object>
    // private
    var root: Node?
    var reprIsShared: bool

    opaque predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr && MutableRepr <= Repr
      ensures Valid() ==> IsSorted(Contents)
    {
      this in MutableRepr && MutableRepr <= Repr &&
      (root == null ==> Contents == []) &&
      (root != null ==>
        root in Repr && root.Repr <= Repr && this !in root.Repr &&
        root.NodeValid() && Contents == root.Contents) &&
      IsSorted(Contents) &&
      (IsReadonly ==> reprIsShared) &&
      (!reprIsShared && root != null ==> root.Repr <= MutableRepr) &&
      (reprIsShared ==> MutableRepr == {this})
    }

    static predicate {:opaque} IsSorted(c: seq<int>)  // checks if "c" is sorted and has no duplicates
    {
      forall i, j :: 0 <= i < j < |c| ==> c[i] < c[j]
    }
    static lemma IsSortedProperty(c: seq<int>)
      ensures IsSorted(c) <==> forall i, j :: 0 <= i < j < |c| ==> c[i] < c[j]
    {
      reveal IsSorted();
    }
    static lemma SmallIsSorted(s: seq<int>)
      ensures |s| <= 1 ==> IsSorted(s)
    {
      reveal IsSorted();
    }
    static predicate AllBelow(s: seq<int>, d: int)
    {
      forall i :: 0 <= i < |s| ==> s[i] < d
    }
    static predicate AllAbove(d: int, s: seq<int>)
    {
      forall i :: 0 <= i < |s| ==> d < s[i]
    }
    static predicate SortedSplit(left: seq<int>, data: int, right: seq<int>)
    {
      IsSorted(left) && IsSorted(right) &&
      AllBelow(left, data) && AllAbove(data, right)
    }
    static lemma SortCombineProperty(left: seq<int>, data: int, right: seq<int>)
      requires SortedSplit(left, data, right)
      ensures IsSorted(left + [data] + right)
    {
      reveal IsSorted();
    }

    constructor Empty()
      ensures Valid() && Contents == [] && !IsReadonly
      ensures MutableRepr <= Repr && fresh(Repr)
    {
      new;
      reveal Valid();
      Contents := [];
      IsReadonly := false;
      MutableRepr := {this};
      Repr := MutableRepr;
      root := null;
      reprIsShared := false;
      SmallIsSorted(Contents);
    }

    method CreateSnapshot() returns (snapshot: Tree)
      requires Valid()
      modifies Repr
      ensures Valid() && fresh(Repr - old(Repr))
      ensures Contents == old(Contents) && IsReadonly == old(IsReadonly)
      ensures snapshot.Valid()
      ensures snapshot.Contents == Contents && snapshot.IsReadonly
      // the mutable part of the original tree is disjoint from the representation of the snapshot
      ensures snapshot.Repr !! MutableRepr
      // representation of the snapshot consists of new things of things from the previous tree (that are now immutable)
      ensures fresh(snapshot.Repr - old(Repr))
    {
      reveal Valid();
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
      requires Valid() && !IsReadonly
      modifies MutableRepr
      ensures Valid() && fresh(Repr - old(Repr)) && fresh(MutableRepr - old(MutableRepr))
      ensures IsReadonly == old(IsReadonly)
      ensures x in old(Contents) ==> pos < 0 && Contents == old(Contents)
      ensures x !in old(Contents) ==>
        0 <= pos < |Contents| == |old(Contents)| + 1 &&
        Contents == old(Contents[..pos] + [x] + Contents[pos..])
    {
      reveal Valid();
      if reprIsShared {
        root, pos := Node.FunctionalInsert(root, x);
        Contents := root.Contents;
        Repr := root.Repr + {this};
        MutableRepr := {this};
      } else if root == null {
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
      requires Valid() // && IsReadonly;
      ensures iter.Valid() && fresh(iter.IterRepr)
      ensures iter.T == this && iter.Contents == Contents && iter.N == -1
    {
      reveal Valid();
      iter := new Iterator.Init(this);
    }

    method Print()
      requires Valid()
      modifies Repr
      ensures Valid() && fresh(Repr - old(Repr))
      ensures Contents == old(Contents) && IsReadonly == old(IsReadonly)
    {
      reveal Valid();
      var s;
      if IsReadonly {
        s := this;
      } else {
        s := CreateSnapshot();
      }
      var it := s.CreateIterator();
      it.Print();
    }
  }

  class Node
  {
    ghost var Contents: seq<int>
    ghost var Repr: set<object>
    var data: int
    var left: Node?
    var right: Node?

    predicate {:opaque} NodeValid()
      reads this, Repr
      ensures NodeValid() ==> this in Repr && Tree.IsSorted(Contents)
    {
      this in Repr &&
      (left != null ==>
        left in Repr && left.Repr <= Repr && this !in left.Repr && left.NodeValid()) &&
      (right != null ==>
        right in Repr && right.Repr <= Repr && this !in right.Repr && right.NodeValid()) &&
      (left != null && right != null ==> left.Repr !! right.Repr) &&
      SortedSplit(left, data, right) &&
      Contents == CombineSplit(left, data, right) &&
      Tree.IsSorted(Contents)
    }

    static predicate SortedSplit(left: Node?, data: int, right: Node?)
      reads left, right
    {
      Tree.SortedSplit(if left == null then [] else left.Contents, data, if right == null then [] else right.Contents)
    }
    static function CombineSplit(left: Node?, data: int, right: Node?): seq<int>
      reads left, right
    {
      if left == null && right == null then
        [data]
      else if left != null && right == null then
        left.Contents + [data]
      else if left == null && right != null then
        [data] + right.Contents
      else
        left.Contents + [data] + right.Contents
    }
    static lemma CombineSortedSplit(left: Node?, data: int, right: Node?)
      requires SortedSplit(left, data, right)
      ensures Tree.IsSorted(CombineSplit(left, data, right))
    {
      var L := if left == null then [] else left.Contents;
      var R := if right == null then [] else right.Contents;
      Tree.SortCombineProperty(L, data, R);
      assert CombineSplit(left, data, right) == L + [data] + R;
    }

    constructor Init(x: int)
      ensures NodeValid() && fresh(Repr)
      ensures Contents == [x]
    {
      Contents := [x];
      Repr := {this};
      left, data, right := null, x, null;
      new;
      Tree.SmallIsSorted([]);
      Tree.SmallIsSorted([x]);
      reveal NodeValid();
    }

    constructor Build(left: Node?, x: int, right: Node?)
      requires left != null ==> left.NodeValid() && Tree.AllBelow(left.Contents, x)
      requires right != null ==> right.NodeValid() && Tree.AllAbove(x, right.Contents)
      requires left != null && right != null ==> left.Repr !! right.Repr
      ensures NodeValid()
      ensures Contents == CombineSplit(left, x, right)
      ensures left == null && right == null ==> fresh(Repr)
      ensures left != null && right == null ==> fresh(Repr - left.Repr)
      ensures left == null && right != null ==> fresh(Repr - right.Repr)
      ensures left != null && right != null ==> fresh(Repr - left.Repr - right.Repr)
    {
      Contents := [x];
      Repr := {this};
      this.left, data, this.right := left, x, right;
      if left != null {
        Contents := left.Contents + Contents;
        Repr := Repr + left.Repr;
      }
      if right != null {
        Contents := Contents + right.Contents;
        Repr := Repr + right.Repr;
      }
      new;
      ghost var L := if left == null then [] else left.Contents;
      ghost var R := if right == null then [] else right.Contents;
      Tree.SmallIsSorted([]);
      CombineSortedSplit(left, x, right);
      reveal NodeValid();
    }

    static method FunctionalInsert(n: Node?, x: int) returns (r: Node, ghost pos: int)
      requires n != null ==> n.NodeValid()
      ensures r.NodeValid()
      ensures n == null ==> fresh(r.Repr)
      ensures n != null ==> fresh(r.Repr - n.Repr)
      ensures n == null ==> r.Contents == [x] && pos == 0
      ensures n != null && x in n.Contents ==> r == n && pos < 0
      ensures n != null && x !in n.Contents ==>
        0 <= pos < |r.Contents| == |n.Contents| + 1 &&
        r.Contents == n.Contents[..pos] + [x] + n.Contents[pos..]
      decreases if n == null then {} else n.Repr
    {
      if n == null {
        r := new Node.Init(x);
        pos := 0;
      } else if x < n.data {
        r, pos := FunctionalInsert_Left(n, x);
      } else if n.data < x {
        r, pos := FunctionalInsert_Right(n, x);
      } else {
        reveal n.NodeValid();
        r, pos := n, -1;
      }
    }

    static method FunctionalInsert_Left(n: Node, x: int) returns (r: Node, ghost pos: int)
      requires n.NodeValid() && x < n.data
      ensures r.NodeValid()
      ensures fresh(r.Repr - n.Repr)
      ensures x in n.Contents ==> r == n && pos < 0
      ensures x !in n.Contents ==>
        0 <= pos < |r.Contents| == |n.Contents| + 1 &&
        r.Contents == n.Contents[..pos] + [x] + n.Contents[pos..]
      decreases n.Repr, 0
    {
      reveal n.NodeValid();
      var left;
      left, pos := FunctionalInsert(n.left, x);
      if left == n.left {
        r, pos := n, -1;
      } else {
        r := new Node.Build(left, n.data, n.right);
      }
    }

    static method FunctionalInsert_Right(n: Node, x: int) returns (r: Node, ghost pos: int)
      requires n.NodeValid() && n.data < x
      ensures r.NodeValid()
      ensures fresh(r.Repr - n.Repr)
      ensures x in n.Contents ==> r == n && pos < 0
      ensures x !in n.Contents ==>
        0 <= pos < |r.Contents| == |n.Contents| + 1 &&
        r.Contents == n.Contents[..pos] + [x] + n.Contents[pos..]
      decreases n.Repr, 0
    {
      reveal n.NodeValid();
      var right;
      right, pos := FunctionalInsert(n.right, x);
      if right == n.right {
        r, pos := n, -1;
      } else {
        ghost var L := if n.left == null then [] else n.left.Contents;
        ghost var Llen := |L| + 1;
        pos := Llen + pos;
        r := new Node.Build(n.left, n.data, right);
      }
    }

    method MutatingInsert(x: int) returns (ghost pos: int)
      requires NodeValid()
      modifies Repr
      ensures NodeValid() && fresh(Repr - old(Repr))
      ensures x in old(Contents) ==> pos < 0 && Contents == old(Contents)
      ensures x !in old(Contents) ==>
        0 <= pos < |Contents| == |old(Contents)| + 1 &&
        Contents == old(Contents[..pos] + [x] + Contents[pos..])
      decreases Repr
    {
      if x < data {
        pos := MutatingInsert_Left(x);
      } else if data < x {
        pos := MutatingInsert_Right(x);
      } else {
        reveal NodeValid();
        pos := -1;
      }
    }

    method MutatingInsert_Left(x: int) returns (ghost pos: int)
      requires NodeValid() && x < data
      modifies Repr
      ensures NodeValid() && fresh(Repr - old(Repr))
      ensures x in old(Contents) ==> pos < 0 && Contents == old(Contents)
      ensures x !in old(Contents) ==>
        0 <= pos < |Contents| == |old(Contents)| + 1 &&
        Contents == old(Contents[..pos] + [x] + Contents[pos..])
      decreases Repr, 0
    {
      reveal NodeValid();
      ghost var R := if right == null then [] else right.Contents;
      Tree.SmallIsSorted([]);
      if left == null {
        left := new Node.Init(x);
        pos := 0;
      } else {
        pos := left.MutatingInsert(x);
      }
      Repr := Repr + left.Repr;
      Contents := left.Contents + [data] + R;
      Tree.SortCombineProperty(left.Contents, data, R);
      reveal NodeValid();
    }

    method MutatingInsert_Right(x: int) returns (ghost pos: int)
      requires NodeValid() && data < x
      modifies Repr
      ensures NodeValid() && fresh(Repr - old(Repr))
      ensures x in old(Contents) ==> pos < 0 && Contents == old(Contents)
      ensures x !in old(Contents) ==>
        0 <= pos < |Contents| == |old(Contents)| + 1 &&
        Contents == old(Contents[..pos] + [x] + Contents[pos..])
      decreases Repr, 0
    {
      reveal NodeValid();
      ghost var L := if left == null then [] else left.Contents;
      ghost var Llen := |L| + 1;
      if right == null {
        right := new Node.Init(x);
        pos := Llen;
      } else {
        pos := right.MutatingInsert(x);
        if pos < 0 {
        } else {
          pos := Llen + pos;
        }
      }
      Repr := Repr + right.Repr;
      Contents := L + [data] + right.Contents;
      Tree.SmallIsSorted([]);
      Tree.SortCombineProperty(L, data, right.Contents);
      reveal NodeValid();
    }
  }

  class Iterator
  {
    // public
    ghost var IterRepr: set<object>  // note, IterRepr does not include T.Repr
    ghost var Contents: seq<int>
    ghost var N: int
    var T: Tree?
    // private
    var initialized: bool
    var stack: List

    opaque predicate Valid()
      reads this, IterRepr, T
      reads if T != null then T.Repr else {}
      ensures Valid() ==> T != null && IterRepr !! T.Repr
    {
      this in IterRepr &&
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
    static opaque predicate R(wlist: List, n: int, C: seq<int>, Nodes: set<object>)
      reads Nodes
      decreases wlist
    {
      match wlist
      case Nil => n == |C|
      case Cons(p, rest) =>
        p in Nodes && p.Repr <= Nodes && p.NodeValid() &&
        0 <= n < |C| && p.data == C[n] &&
        (reveal p.NodeValid();
         R(rest, n + 1 + if p.right==null then 0 else |p.right.Contents|, C, Nodes) &&
         p.Contents[if p.left==null then 0 else |p.left.Contents| ..] <= C[n..])
    }

    constructor Init(t: Tree)
      requires t.Valid()
      ensures Valid() && fresh(IterRepr)
      ensures T == t && Contents == t.Contents && N == -1
    {
      new;
      reveal Valid();
      reveal t.Valid();
      reveal R();
      Init_Aux(t);
    }
    method Init_Aux(t: Tree)
      requires this !in t.Repr
      // The following three lines say what it is we need from t.Valid():
      requires t.root == null ==> |t.Contents| == 0
      requires t.root != null ==> t.root in t.Repr && t.root.Repr <= t.Repr && t.root.NodeValid()
      requires t.root != null ==> t.root.Contents <= t.Contents && |t.Contents| == |t.root.Contents|
      modifies this
      ensures t.Valid() ==> Valid()
      ensures fresh(IterRepr - {this})
      ensures T == t && Contents == t.Contents && N == -1
    {
      reveal Valid();
      reveal R();
      T := t;
      IterRepr := {this};
      Contents := T.Contents;
      initialized, stack, N := false, Nil, -1;
      if t.root != null {
        stack := Push(stack, 0, t.root, Contents, T.Repr);
      }
    }

    method Print()
      requires Valid()
      modifies IterRepr
    {
      reveal Valid();
      reveal R();
      print "Tree:";
      var more := MoveNext();
      while more
        invariant Valid()
        invariant more ==> 0 <= N < |Contents|
        invariant fresh(IterRepr - old(IterRepr))
        decreases |Contents| - N
      {
        var x := Current();
        print " ", x;
        more := MoveNext();
      }
      print "\n";
    }

    // private
    static method {:vcs_split_on_every_assert} Push(stIn: List, ghost n: int, p: Node, ghost C: seq<int>, ghost Nodes: set<object>) returns (st: List)
      requires p in Nodes && p.Repr <= Nodes && p.NodeValid()
      requires 0 <= n <= |C|
      requires p.Contents <= C[n..]
      requires R(stIn, n + |p.Contents|, C, Nodes)
      ensures R(st, n, C, Nodes)
      decreases |p.Contents|
    {
      st := Cons(p, stIn);

      reveal R();
      reveal p.NodeValid();
      if p.left != null {
        st := Push(st, n, p.left, C, Nodes);
      }
    }

    method Current() returns (x: int)
      requires Valid() && 0 <= N < |Contents|
      ensures x == Contents[N]
    {
      reveal Valid();
      reveal R();
      match (stack)
      case Cons(y, rest) => x := y.data;
    }

    method {:vcs_split_on_every_assert} MoveNext() returns (hasCurrent: bool)
      requires Valid() && N <= |Contents|
      modifies IterRepr
      ensures Valid() && fresh(IterRepr - old(IterRepr)) && T.Repr == old(T.Repr)
      ensures Contents == old(Contents) && T == old(T)
      ensures old(N) < |Contents| ==> N == old(N) + 1
      ensures old(N) == |Contents| ==> N == old(N)
      ensures hasCurrent <==> 0 <= N < |Contents|
    {
      reveal Valid();
      if !initialized {
        initialized, N := true, 0;
        hasCurrent := stack != Nil;
      } else {
        match (stack)
        case Nil =>
          hasCurrent := false;
        case Cons(p, rest) =>
          // lemmas:
          reveal p.NodeValid();

          stack, N := rest, N+1;

          if p.right != null {
            reveal R();
            reveal p.right.NodeValid();
            assert p.right.Contents <= Contents[N..];
            stack := Push(stack, N, p.right, Contents, T.Repr);
          }
          hasCurrent := stack != Nil;
      }
      reveal R();
    }
  }

}  // module SnapTree
