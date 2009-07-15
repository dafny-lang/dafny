class Node {
  var next: Node;

  function IsList(r: set<Node>): bool
    reads this, r; 
  {
    next != null  ==>  next.IsList(r - {this})
  }

  method Test(n: Node, nodes: set<Node>) 
  {
    assume nodes == nodes - {n};
    // the next line needs the Set extensionality axiom, the antecedent of
    // which is supplied by the previous line
    assert IsList(nodes) == IsList(nodes - {n});
  }

  method Create()
    modifies this;
  {
    next := null;
    var tmp: Node;
    tmp := new Node;
    assert tmp != this;  // was once a bug in the Dafny checker
  }
}
