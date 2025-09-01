// RUN: %testDafnyForEachResolver "%s" -- --allow-deprecation --verification-time-limit=90


// Schorr-Waite algorithms, written and verified in Dafny.
// Rustan Leino
// Original version:  7 November 2008
// Version with proof divided into stages:  June 2012.

abstract module M0 {
  // In this module, we declare the Node class, the definition of Reachability, and the specification
  // and implementation of the Schorr-Waite algorithm.

  class Node {
    var children: seq<Node?>
    var marked: bool
    var childrenVisited: nat
  }

  datatype Path = Empty | Extend(Path, Node)

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
    decreases *  // leave termination checking for a later refinement
  {
    root.marked := true;
    var t, p: Node? := root, null;
    ghost var stackNodes: seq<Node> := [];
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
                  stackNodes[0].children[stackNodes[0].childrenVisited] == null
      invariant forall k {:matchinglooprewrite false} :: 0 < k < |stackNodes| ==>
                  stackNodes[k].children[stackNodes[k].childrenVisited] == stackNodes[k-1]
      // We also need to keep track of what the original values of the children pointers had been.  Here, we
      // have that the active child of stackNodes[k] used to be stackNodes[k+1], with the end case pointing
      // to t.
      invariant forall k {:matchinglooprewrite false} :: 0 <= k < |stackNodes|-1 ==>
                  old(stackNodes[k].children)[stackNodes[k].childrenVisited] == stackNodes[k+1]
      invariant 0 < |stackNodes| ==>
        old(stackNodes[|stackNodes|-1].children)[stackNodes[|stackNodes|-1].childrenVisited] == t

      decreases *  // leave termination checking for a later refinement
    {
      if t.childrenVisited == |t.children| {
        // pop
        t.childrenVisited := 0;
        if p == null { break; }

        t, p, p.children := p, p.children[p.childrenVisited], p.children[p.childrenVisited := t];
        stackNodes := stackNodes[..|stackNodes| - 1];
        t.childrenVisited := t.childrenVisited + 1;

      } else if t.children[t.childrenVisited] == null || t.children[t.childrenVisited].marked {
        // just advance to next child
        t.childrenVisited := t.childrenVisited + 1;

      } else {
        // push
        stackNodes := stackNodes + [t];
        t, p, t.children := t.children[t.childrenVisited], t, t.children[t.childrenVisited := p];
        t.marked := true;

        // To prove that this "if" branch maintains the invariant "t !in stackNodes" will require
        // some more properties about the loop.  Therefore, we just assume the property here and
        // prove it in a separate refinement.
        assume t !in stackNodes;
      }
    }
    // From the loop invariant, it now follows that all children pointers have been restored,
    // and so have all .childrenVisited fields.  Thus, the last postcondition (the one that says
    // the structure of the graph has not been changed) has been established.
    // Eventually, we also need to prove that exactly the right nodes have been marked,
    // but let's just assume those properties for now and prove them in later refinements:
    assume root.marked && forall n :: n in S && n.marked ==>
                forall ch :: ch in n.children && ch != null ==> ch.marked;
    assume forall n :: n in S && n.marked ==> old(Reachable(root, n, S));
  }
}

abstract module M1 refines M0 {
  // In this superposition, we start reasoning about the marks.  In particular, we prove that the method
  // marks all reachable nodes.
  method SchorrWaite...
  {
    ...;
    while ...
      // The loop keeps marking nodes:  The root is always marked.  All children of any marked non-active
      // node are marked.  Active nodes are marked, and the first .childrenVisited of every active node
      // are marked.
      invariant root.marked
      invariant forall n :: n in S && n.marked && n !in stackNodes && n != t ==>
                  forall ch :: ch in n.children && ch != null ==> ch.marked
      invariant forall n :: n in stackNodes || n == t ==>
                  n.marked &&
                  forall j :: 0 <= j < n.childrenVisited ==> n.children[j] == null || n.children[j].marked
    {
      if ... {  // pop
      } else if ... {  // next child
      } else {  // push
        ...;
        // With the new loop invariants, we know that all active nodes are marked.  Since the new value
        // of "t" was not marked at the beginning of this iteration, we can now prove that the invariant
        // "t !in stackNodes" is maintained, so we'll refine the assume from above with an assert.
        assert ...;
      }
    }
    // The new loop invariants give us a lower bound on which nodes are marked.  Hence, we can now
    // discharge the "everything reachable is marked" postcondition, whose proof we postponed above
    // by supplying an assume statement.  Here, we refine that assume statement into an assert.
    assert ...;
    assume ...;
  }
}

abstract module M2 refines M1 {
  // In this superposition, we prove that only reachable nodes are marked.  Essentially, we want
  // to add a loop invariant that says t is reachable from root, because then the loop invariant
  // that marked nodes are reachable follows.  More precisely, we need to say that the node
  // referenced by t is *in the initial state* reachable from root--because as we change
  // children pointers during the course of the algorithm, what is reachable at some point in
  // time may be different from what was reachable initially.

  // To do our proof, which involves establishing reachability between various nodes, we need
  // some additional bookkeeping.  In particular, we keep track of the path from root to t,
  // and we associate with every marked node the path to it from root.  The former is easily
  // maintained in a local ghost variable; the latter is most easily represented as a ghost
  // field in each node (an alternative would be to have a local variable that is a map from
  // nodes to paths).  So, we add a field declaration to the Node class:
  class Node ... {
    ghost var pathFromRoot: Path
  }

  method SchorrWaite...
  {
    ghost var path := Path.Empty;
    root.pathFromRoot := path;
    ...;
    while ...
      // There's a subtle complication when we speak of old(ReachableVia(... P ...)) for a path
      // P.  The expression old(...) says to evaluate the expression "..." in the pre-state of
      // the method.  So, old(ReachableVia(...)) says to evaluate ReachableVia(...) in the pre-
      // state of the method.  But in order for the "old(...)" expression to be well-formed,
      // the subexpressions of the "..." must only refer to values that existed in the pre-state
      // of the method.  This incurs the proof obligation that any objects referenced by the
      // parameters of ReachableVia(...) must have been allocated in the pre-state of the
      // method.  The proof obligation is easy to establish for root, t, and S (since root and
      // S were given as in-parameters to the method, and we have "t in S").  But what about
      // the path argument to ReachableVia?  Since datatype values of type Path contain object
      // references, we need to make sure we can deal with the proof obligation for the path
      // argument.  For this reason, we add invariants that say that "path" and the .pathFromRoot
      // field of all marked nodes contain values that make sense in the pre-state.
      invariant old(allocated(path)) && old(ReachableVia(root, path, t, S))
      invariant forall n :: n in S && n.marked ==> var pth := n.pathFromRoot;
                  old(allocated(pth)) && old(ReachableVia(root, pth, n, S))
      invariant forall n :: n in S && n.marked ==> old(Reachable(root, n, S))
    {
      if ... {
        // pop
        ...;
        path := t.pathFromRoot;
      } else if ... {
        // advance to next child
      } else {
        // push
        path := Path.Extend(path, t);
        ...;
        t.pathFromRoot := path;
      }
    }
    // In M0 above, we placed two assume statements here.  In M1, we refined the first of these
    // into an assert.  We repeat that assert here:
    assert ...;
    // And now we we refine the second assume into an assert, proving that only reachable nodes
    // have been marked.
    assert ...;
  }
}

module M3 refines M2 {
  // In this final superposition, we prove termination of the loop.
  method SchorrWaite...
    decreases true  // say that the method is now one that is proved to terminate (note, the value
                    // 'true' is arbitrary; we just need to supply _some_ decreases clause so that
                    // the 'decreases *' from above is not inherited)
  {
    // The loop variant is a lexicographic triple, consisting of (0) the set of unmarked
    // nodes, (1) the (length of the) stackNodes sequence, and (2) the number children of
    // the current node that are still to be investigated.  We introduce a ghost variable
    // to keep track of the set of unmarked nodes.
    ghost var unmarkedNodes := S - {root};
    ...;
    while ...
      invariant forall n :: n in S && !n.marked ==> n in unmarkedNodes
      decreases unmarkedNodes, stackNodes, |t.children| - t.childrenVisited
    {
      if ... {  // pop
      } else if ... {  // next child
      } else {  // push
        ...;
        unmarkedNodes := unmarkedNodes - {t};
      }
    }
  }
}
