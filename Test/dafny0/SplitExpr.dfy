class UnboundedStack<T> {
  var top: Node<T>;
  ghost var footprint: set<object>;
  ghost var content: seq<T>; 

  function IsUnboundedStack(): bool
    reads {this} + footprint;
  {
    this in footprint &&
    (top == null  ==>  content == []) &&
    (top != null  ==>  top in footprint && top.footprint <= footprint &&
                       top.prev == null && content == top.content && top.Valid())
  }

  function IsEmpty(): bool
    reads {this};
  { content == [] }

  method Pop() returns (result: T)
    requires IsUnboundedStack() && !IsEmpty();
    modifies footprint;
    ensures IsUnboundedStack() && content == old(content)[1..];
  {
    result := top.val;
    // The following assert does the trick, because it gets inlined and thus
    // exposes top.next.Valid() (if top.next != null):
    footprint := footprint - top.footprint;  top := top.next;
    // In a previous version of the implementation of the SplitExpr transformation, the
    // following assert did not have the intended effect of being used as a lemma:
    assert top != null ==> top.Valid();
    if (top != null) {
      footprint := footprint + top.footprint;  top.prev := null;
    }
    content := content[1..];
} }

class Node<T> {
  var val: T;  
  var next: Node<T>;
  var prev: Node<T>;
  var footprint: set<Node<T>>;
  var content: seq<T>;

  function Valid(): bool
    reads this, footprint;
  {
    this in footprint && !(null in footprint) &&
    (next == null  ==>  content == [val])  &&
    (next != null  ==>  next in footprint &&
                        next.footprint < footprint &&
                        !(this in next.footprint) &&
                        next.prev == this &&
                        content == [val] + next.content &&
                        next.Valid())
  }
}
