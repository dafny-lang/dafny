// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Rustan Leino
// 7 November 2008
// Schorr-Waite and other marking algorithms, written and verified in Dafny.

class Node {
  var children: seq<Node?>
  var marked: bool
  var childrenVisited: nat
  ghost var pathFromRoot: Path
}

datatype Path = Empty | Extend(Path, Node)

// ---------------------------------------------------------------------------------

method RecursiveMark(root: Node, ghost S: set<Node>)
  requires root in S
  // S is closed under 'children':
  requires forall n :: n in S ==>
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
              forall ch :: ch in n.children ==> ch == null || ch in S
  requires forall n :: n in S && n.marked ==>
              n in stackNodes ||
              forall ch :: ch in n.children && ch != null ==> ch.marked
  requires forall n :: n in stackNodes ==> n.marked
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
  ghost var unmarkedNodes := S - {t};
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
      assert {:focus} true;
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
      assert {:focus} true;
      // push
      stackNodes := stackNodes + [t];
      t := t.children[t.childrenVisited];
      t.marked := true;
      unmarkedNodes := unmarkedNodes - {t};
    }
  }
}

// ---------------------------------------------------------------------------------

ghost predicate Reachable(source: Node, sink: Node, S: set<Node>)
  reads S
{
  exists via :: ReachableVia(source, via, sink, S)
}

ghost predicate ReachableVia(source: Node, older p: Path, sink: Node, S: set<Node>)
  reads S
  decreases p
{
  match p
  case Empty => source == sink
  case Extend(prefix, n) => n in S && sink in n.children && ReachableVia(source, prefix, n, S)
}

method SchorrWaite(root: Node, ghost S: set<Node>)
  requires root in S
  // S is closed under 'children':
  requires forall n :: n in S ==>
              forall ch :: ch in n.children ==> ch == null || ch in S
  // the graph starts off with nothing marked and nothing being indicated as currently being visited:
  requires forall n :: n in S ==> !n.marked && n.childrenVisited == 0
  modifies S
  // nodes reachable from 'root' are marked:
  ensures root.marked
  ensures forall n :: n in S && n.marked ==>
              forall ch :: ch in n.children && ch != null ==> ch.marked
  // every marked node was reachable from 'root' in the pre-state:
  ensures forall n :: n in S && n.marked ==> old(Reachable(root, n, S))
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
    // stackNodes is a sequence of nodes from S:
    invariant forall i :: 0 <= i < |stackNodes| ==> stackNodes[i] in S

    // The current node, t, is not included in stackNodes.  Rather, t is just above the top of stackNodes.
    // We say that the stack stackNodes+[t] are the "active" nodes.
    invariant t in S && t !in stackNodes

    // p points to the parent of the current node, that is, the node through which t was encountered in the
    // depth-first traversal.  This amounts to being the top of stackNodes, or null if stackNodes is empty.
    // Note, it may seem like the variable p is redundant, since it holds a value that can be computed
    // from stackNodes.  But note that stackNodes is a ghost variable and won't be present at run
    // time, where p is a physical variable that will be present at run time.
    invariant p == if |stackNodes| == 0 then null else stackNodes[|stackNodes|-1]

    // The .childrenVisited field is the extra information that the Schorr-Waite algorithm needs.  It
    // is used only for the active nodes, where it keeps track of how many of a node's children have been
    // processed.  For the nodes on stackNodes, .childrenVisited is less than the number of children, so
    // it is an index of a child.  For t, .childrenVisited may be as large as all of the children, which
    // indicates that the node is ready to be popped off the stack of active nodes.  For all other nodes,
    // .childrenVisited is the original value, which is 0.
    invariant forall n :: n in stackNodes ==> n.childrenVisited < |n.children|
    invariant t.childrenVisited <= |t.children|
    invariant forall n :: n in S && n !in stackNodes && n != t ==> n.childrenVisited == 0

    // To represent the stackNodes, the algorithm reverses children pointers.  It never changes the number
    // of children a node has.  The only nodes with children pointers different than the original values are
    // the nodes on stackNodes; moreover, only the index of the currently active child of a node is different.
    invariant forall n :: n in stackNodes ==>
                |n.children| == old(|n.children|) &&
                forall j :: 0 <= j < |n.children| ==> j == n.childrenVisited || n.children[j] == old(n.children[j])
    invariant forall n :: n in S && n !in stackNodes ==> n.children == old(n.children)

    // The children pointers that have been changed form a stack.  That is, the active child of stackNodes[k]
    // points to stackNodes[k-1], with the end case pointing to null.
    invariant 0 < |stackNodes| ==>
                stackNodes[0].children[assert stackNodes[0] in stackNodes; assert stackNodes[0].childrenVisited < |stackNodes[0].children|; stackNodes[0].childrenVisited] == null
    invariant forall k {:matchinglooprewrite false} :: 0 < k < |stackNodes| ==>
                stackNodes[k].children[stackNodes[k].childrenVisited] == stackNodes[k-1]
    // We also need to keep track of what the original values of the children pointers had been.  Here, we
    // have that the active child of stackNodes[k] used to be stackNodes[k+1], with the end case pointing
    // to t.
    invariant forall k {:matchinglooprewrite false} :: 0 <= k < |stackNodes|-1 ==>
                old(stackNodes[k].children)[stackNodes[k].childrenVisited] == stackNodes[k+1]
    invariant 0 < |stackNodes| ==>
      old(stackNodes[|stackNodes|-1].children)[stackNodes[|stackNodes|-1].childrenVisited] == t

    invariant root.marked
    invariant forall n :: n in S && n.marked && n !in stackNodes && n != t ==>
                forall ch :: ch in n.children && ch != null ==> ch.marked
    invariant forall n :: n in stackNodes || n == t ==>
                n.marked &&
                forall j :: 0 <= j < n.childrenVisited ==> n.children[j] == null || n.children[j].marked

    invariant old(allocated(path)) && old(ReachableVia(root, path, t, S))
    invariant forall n :: n in S && n.marked ==> var pth := n.pathFromRoot;
                old(allocated(pth)) && old(ReachableVia(root, pth, n, S))
    invariant forall n :: n in S && n.marked ==> old(Reachable(root, n, S))

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
      assert {:focus} true;
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
