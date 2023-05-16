// RUN: %dafny /allocated:1 /compile:0 /dprint:"%t.dprint" /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Rustan Leino
// 7 November 2008
// Schorr-Waite and other marking algorithms, written and verified in Dafny.
// Copyright (c) 2008, Microsoft.

class Node {
  var children: seq<Node?>
  var marked: bool
  var childrenVisited: int
  ghost var pathFromRoot: Path
}

datatype Path = Empty | Extend(Path, Node)


class Main {
  method RecursiveMark(root: Node, ghost S: set<Node>)
    requires root in S
    // S is closed under 'children':
    requires forall n :: n in S ==>
                allocated(n) &&
                forall ch :: ch in n.children ==> ch == null || ch in S
    requires forall n :: n in S ==> !n.marked && n.childrenVisited == 0
    modifies S
    ensures root.marked
    // nodes reachable from 'root' are marked:
    ensures forall n :: n in S && n.marked ==>
                forall ch :: ch in n.children && ch != null ==> ch.marked
    ensures forall n :: n in S ==>
                n.childrenVisited == old(n.childrenVisited) &&
                n.children == old(n.children)
  {
    RecursiveMarkWorker(root, S, {});
  }

  method RecursiveMarkWorker(root: Node, ghost S: set<Node>, ghost stackNodes: set<Node>)
    requires root in S
    requires forall n :: n in S ==>
                allocated(n) &&
                forall ch :: ch in n.children ==> ch == null || ch in S
    requires forall n :: n in S && n.marked ==>
                n in stackNodes ||
                forall ch :: ch in n.children && ch != null ==> ch.marked
    requires forall n :: n in stackNodes ==> allocated(n) && n.marked
    modifies S
    ensures root.marked
    // nodes reachable from 'root' are marked:
    ensures forall n :: n in S && n.marked ==>
                n in stackNodes ||
                forall ch :: ch in n.children && ch != null ==> ch.marked
    ensures forall n :: n in S && old(n.marked) ==> n.marked
    ensures forall n :: n in S ==>
                n.childrenVisited == old(n.childrenVisited) &&
                n.children == old(n.children)
    decreases S - stackNodes
  {
    if !root.marked {
      root.marked := true;
      var i := 0;
      while i < |root.children|
        invariant root.marked && i <= |root.children|
        invariant forall n :: n in S && n.marked ==>
                n == root ||
                n in stackNodes ||
                forall ch :: ch in n.children && ch != null ==> ch.marked
        invariant forall j :: 0 <= j < i ==>
                    root.children[j] == null || root.children[j].marked
        invariant forall n :: n in S && old(n.marked) ==> n.marked
        invariant forall n :: n in S ==>
                n.childrenVisited == old(n.childrenVisited) &&
                n.children == old(n.children)
      {
        var c := root.children[i];
        if c != null {
          RecursiveMarkWorker(c, S, stackNodes + {root});
        }
        i := i + 1;
      }
    }
  }

  // ---------------------------------------------------------------------------------

  method IterativeMark(root: Node, ghost S: set<Node>)
    requires root in S
    // S is closed under 'children':
    requires forall n :: n in S ==>
                allocated(n) &&
                forall ch :: ch in n.children ==> ch == null || ch in S
    requires forall n :: n in S ==> !n.marked && n.childrenVisited == 0
    modifies S
    ensures root.marked
    // nodes reachable from 'root' are marked:
    ensures forall n :: n in S && n.marked ==>
                forall ch :: ch in n.children && ch != null ==> ch.marked
    ensures forall n :: n in S ==>
                n.childrenVisited == old(n.childrenVisited) &&
                n.children == old(n.children)
  {
    var t := root;
    t.marked := true;
    var stackNodes: seq<Node> := [];
    ghost var unmarkedNodes: set<Node> := S - {t};
    while true
      invariant root.marked && t in S && t !in stackNodes
      // stackNodes has no duplicates:
      invariant forall i, j :: 0 <= i < j < |stackNodes| ==>
                  stackNodes[i] != stackNodes[j]
      invariant forall n :: n in stackNodes ==> n in S
      invariant forall n :: n in stackNodes || n == t ==>
                  n.marked &&
                  0 <= n.childrenVisited <= |n.children| &&
                  forall j :: 0 <= j < n.childrenVisited ==>
                    n.children[j] == null || n.children[j].marked
      invariant forall n :: n in stackNodes ==> n.childrenVisited < |n.children|
      // nodes on the stack are linked:
      invariant forall j :: 0 <= j && j+1 < |stackNodes| ==>
                  stackNodes[j].children[stackNodes[j].childrenVisited] == stackNodes[j+1]
      invariant 0 < |stackNodes| ==>
        stackNodes[|stackNodes|-1].children[stackNodes[|stackNodes|-1].childrenVisited] == t
      invariant forall n :: n in S && n.marked && n !in stackNodes && n != t ==>
                  forall ch :: ch in n.children && ch != null ==> ch.marked
      invariant forall n :: n in S && n !in stackNodes && n != t ==>
                  n.childrenVisited == old(n.childrenVisited)
      invariant forall n :: n in S ==> n.children == old(n.children)
      invariant forall n :: n in S && !n.marked ==> n in unmarkedNodes
      decreases unmarkedNodes, stackNodes, |t.children| - t.childrenVisited
    {
      if t.childrenVisited == |t.children| {
        // pop
        t.childrenVisited := 0;
        if |stackNodes| == 0 {
          return;
        }
        t := stackNodes[|stackNodes| - 1];
        stackNodes := stackNodes[..|stackNodes| - 1];
        t.childrenVisited := t.childrenVisited + 1;
      } else if t.children[t.childrenVisited] == null || t.children[t.childrenVisited].marked {
        // just advance to next child
        t.childrenVisited := t.childrenVisited + 1;
      } else {
        // push
        stackNodes := stackNodes + [t];
        t := t.children[t.childrenVisited];
        t.marked := true;
        unmarkedNodes := unmarkedNodes - {t};
      }
    }
  }

  // ---------------------------------------------------------------------------------

  ghost predicate Reachable(from: Node, to: Node, S: set<Node>)
    reads S
  {
    exists via :: ReachableVia(from, via, to, S)
  }

  ghost predicate ReachableVia(from: Node, via: Path, to: Node, S: set<Node>)
    reads S
    decreases via
  {
    match via
    case Empty => from == to
    case Extend(prefix, n) => n in S && allocated(n) && to in n.children && ReachableVia(from, prefix, n, S)
  }

  method SchorrWaite(root: Node, ghost S: set<Node>)
    requires root in S
    // S is closed under 'children':
    requires forall n :: n in S ==>
                allocated(n) &&
                forall ch :: ch in n.children ==> ch == null || ch in S
    // the graph starts off with nothing marked and nothing being indicated as currently being visited:
    requires forall n :: n in S ==> !n.marked && n.childrenVisited == 0
    modifies S
    // nodes reachable from 'root' are marked:
    ensures root.marked
    ensures forall n :: n in S && n.marked ==>
                forall ch :: ch in n.children && ch != null ==> ch.marked
    // every marked node was reachable from 'root' in the pre-state:
    ensures forall n {:autotriggers false} :: n in S && n.marked ==> old(Reachable(root, n, S))
    // the structure of the graph has not changed:
    ensures forall n :: n in S ==>
                n.childrenVisited == old(n.childrenVisited) &&
                n.children == old(n.children)
  {
    var t := root;
    var p: Node? := null;  // parent of t in original graph
    ghost var path := Path.Empty;
    t.marked := true;
    t.pathFromRoot := path;
    ghost var stackNodes: seq<Node> := [];
    ghost var unmarkedNodes := S - {t};
    while true
      invariant root.marked && t in S && t !in stackNodes
      invariant |stackNodes| == 0 <==> p == null
      invariant 0 < |stackNodes| ==> p == stackNodes[|stackNodes|-1]
      // stackNodes has no duplicates:
      invariant forall i, j :: 0 <= i < j < |stackNodes| ==>
                  stackNodes[i] != stackNodes[j]
      invariant forall n :: n in stackNodes ==> n in S
      invariant forall n :: n in stackNodes || n == t ==>
                  n.marked &&
                  0 <= n.childrenVisited <= |n.children| &&
                  forall j :: 0 <= j < n.childrenVisited ==>
                    n.children[j] == null || n.children[j].marked
      invariant forall n :: n in stackNodes ==> n.childrenVisited < |n.children|
      invariant forall n {:trigger n.children} {:trigger n in stackNodes} {:trigger n in S} :: n in S && n.marked && n !in stackNodes && n != t ==>
                  forall ch :: ch in n.children && ch != null ==> ch.marked
      invariant forall n :: n in S && n !in stackNodes && n != t ==>
                  n.childrenVisited == old(n.childrenVisited)
      invariant forall n :: n in S ==> n in stackNodes || (allocated(n) && n.children == old(n.children))
      invariant forall n :: n in stackNodes ==>
                  |n.children| == old(|n.children|) &&
                  forall j :: 0 <= j < |n.children| ==>
                    j == n.childrenVisited || n.children[j] == old(n.children[j])
      // every marked node is reachable:
      invariant old(allocated(path))  // needed to show 'path' worthy as argument to old(Reachable(...))
      invariant old(ReachableVia(root, path, t, S))
      invariant forall n :: n in S && n.marked ==> var pth := n.pathFromRoot; old(allocated(pth))
      invariant forall n :: n in S && n.marked ==> var pth := n.pathFromRoot; old(ReachableVia(root, pth, n, S))
      invariant forall n :: n in S && n.marked ==> old(Reachable(root, n, S))
      // the current values of m.children[m.childrenVisited] for m's on the stack:
      invariant 0 < |stackNodes| ==> stackNodes[0].children[stackNodes[0].childrenVisited] == null
      invariant forall k :: 1 < k < |stackNodes| ==>
                  stackNodes[k].children[stackNodes[k].childrenVisited] != null
      invariant forall k :: 0 < k < |stackNodes| ==>
                  stackNodes[k].children[stackNodes[k].childrenVisited] == stackNodes[k-1]
      // the original values of m.children[m.childrenVisited] for m's on the stack:
      invariant forall k :: 0 <= k && k+1 < |stackNodes| ==>
                  old(stackNodes[k].children)[stackNodes[k].childrenVisited] == stackNodes[k+1]
      invariant 0 < |stackNodes| ==>
        old(stackNodes[|stackNodes|-1].children)[stackNodes[|stackNodes|-1].childrenVisited] == t
      invariant forall n :: n in S && !n.marked ==> n in unmarkedNodes
      decreases unmarkedNodes, stackNodes, |t.children| - t.childrenVisited
    {
      if t.childrenVisited == |t.children| {
        assert {:focus} true;
        // pop
        t.childrenVisited := 0;
        if p == null {
          return;
        }
        var oldP := p.children[p.childrenVisited];
        p.children := p.children[p.childrenVisited := t];
        t := p;
        p := oldP;
        stackNodes := stackNodes[..|stackNodes| - 1];
        t.childrenVisited := t.childrenVisited + 1;
        path := t.pathFromRoot;

      } else if t.children[t.childrenVisited] == null || t.children[t.childrenVisited].marked {
        // just advance to next child
        t.childrenVisited := t.childrenVisited + 1;

      } else {
        assert {:focus} true;
        // push

        var newT := t.children[t.childrenVisited];
        t.children := t.children[t.childrenVisited := p];
        p := t;
        stackNodes := stackNodes + [t];
        path := Path.Extend(path, t);
        t := newT;
        t.marked := true;
        t.pathFromRoot := path;
        unmarkedNodes := unmarkedNodes - {t};
      }
    }
  }
}
