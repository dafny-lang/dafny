// Minimal example
// (Dafny 2.3.0.10506)

abstract module ModuleA {
  datatype Node = Node(x: seq<int>, y: seq<int>)

  predicate good_node(node: Node) {
      && |node.y| == |node.x| + 1
      && (forall i :: 0 <= i < |node.x| ==>
          && node.x[i] == node.y[i]
          && node.x[i] == node.y[i+1])
  }
}

abstract module ModuleB {
  import MA = ModuleA
  import opened M : ModuleA

  lemma A(node: MA.Node, i: int)
  requires MA.good_node(node)
  {
    // This assert fails to verify:
    assert (forall i :: 0 <= i < |node.x| ==>
        && node.x[i] == node.y[i]
        && node.x[i] == node.y[i+1]);
  }

  lemma B(node: Node, i: int)
  requires good_node(node)
  {
    // This assert fails to verify:
    assert (forall i :: 0 <= i < |node.x| ==>
        && node.x[i] == node.y[i]);
  }

  lemma C(node: Node, i: int)
  requires good_node(node)
  {
    // This works:
    assert (forall i :: 0 <= i < |node.x| ==>
        && node.x[i] == node.y[i+1]);
  }
}
