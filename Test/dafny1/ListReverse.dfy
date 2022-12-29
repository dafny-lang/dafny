// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Node {
  var nxt: Node?

  method ReverseInPlace(x: Node?, r: set<Node>) returns (reverse: Node?)
    requires x == null || x in r;
    requires (forall y :: y in r ==> y.nxt == null || y.nxt in r);  // region closure
    modifies r;
    ensures reverse == null || reverse in r;
    ensures (forall y :: y in r ==> y.nxt == null || y.nxt in r);  // region closure
    decreases *;
  {
    var current: Node? := x;
    reverse := null;
    while (current != null)
      invariant current == null || current in r;
      invariant reverse == null || reverse in r;
      invariant (forall y :: y in r ==> y.nxt == null || y.nxt in r);  // region closure
      decreases *;  // omit loop termination check
    {
      var tmp := current.nxt;
      current.nxt := reverse;
      reverse := current;
      current := tmp;
    }
  }
}
