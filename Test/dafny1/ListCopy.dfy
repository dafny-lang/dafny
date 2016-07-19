// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Node {
  var nxt: Node;

  method Init()
    modifies this;
    ensures nxt == null;
  {
    nxt := null;
  }

  method Copy(root: Node) returns (result: Node)
    decreases *;
  {
    var existingRegion: set<Node>;
    assume root == null || root in existingRegion;
    assume (forall o: Node :: o != null && o in existingRegion && o.nxt != null ==> o.nxt in existingRegion);

    var newRoot := null;
    var oldListPtr := root;
    var newRegion: set<Node> := {};

    if (oldListPtr != null) {
      newRoot := new Node.Init();
      newRegion := newRegion + {newRoot};
      var prev := newRoot;

      while (oldListPtr != null)
        invariant newRoot in newRegion;
        invariant (forall o: Node :: o in newRegion ==> o != null);
        invariant (forall o: Node :: o in newRegion && o.nxt != null ==> o.nxt in newRegion);
        invariant prev in newRegion;
        invariant fresh(newRegion);
        invariant newRegion !! existingRegion;
        decreases *;  // omit loop termination check
      {
        var tmp := new Node.Init();

        newRegion := newRegion + {tmp};
        prev.nxt := tmp;

        prev := tmp;
        oldListPtr := oldListPtr.nxt;
      }
    } 
    result := newRoot;
    assert result == null || result in newRegion;
    
    // everything in newRegion is fresh
    assert fresh(newRegion);

    // newRegion # exisitingRegion
    assert newRegion !! existingRegion; 
  }
}
