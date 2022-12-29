// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class UnboundedStack<T> {
  ghost var representation: set<object>
  ghost var content: seq<T>
  var top: Node?<T>

  predicate IsUnboundedStack()
    reads this, representation
  {
    this in representation &&
    (top == null ==>
      content == []) &&
    (top != null ==>
      top in representation && this !in top.footprint && top.footprint <= representation &&
      content == top.content &&
      top.Valid())
  }

  method InitUnboundedStack()
    modifies this
    ensures IsUnboundedStack()
    ensures content == []
  {
    this.top := null;
    this.content := [];
    this.representation := {this};
  }

  method Push(val: T)
    requires IsUnboundedStack()
    modifies this
    ensures IsUnboundedStack()
    ensures content == [val] + old(content)
  {
    top := new Node<T>.InitNode(val,top);
    representation := representation + top.footprint;
    content := [val] + content;
  }

  method Pop() returns (result: T)
    requires IsUnboundedStack()
    requires content != []
    modifies this
    ensures IsUnboundedStack()
    ensures content == old(content)[1..]
  {
    result := top.val;
    top := top.next;
    content := content[1..];
  }

  method isEmpty() returns (result: bool)
    requires IsUnboundedStack()
    ensures result <==> content == []
  {
    result := top == null;
  }
}

class Node<T> {
  ghost var footprint: set<object>
  ghost var content: seq<T>
  var val: T
  var next: Node?<T>

  predicate Valid()
    reads this, footprint
  {
    this in footprint &&
    (next == null ==>
      content == [val]) &&
    (next != null ==>
      next in footprint && next.footprint <= footprint && this !in next.footprint &&
      content == [val] + next.content &&
      next.Valid())
  }

  constructor InitNode(val: T, next: Node?<T>)
    requires next != null ==> next.Valid()
    ensures Valid()
    ensures next != null ==> content == [val] + next.content &&
                             footprint == {this} + next.footprint
    ensures next == null ==> content == [val] &&
                             footprint == {this}
  {
    this.val := val;
    this.next := next;
    if next == null {
      this.footprint := {this};
      this.content := [val];
    } else {
      this.footprint := {this} + next.footprint;
      this.content := [val] + next.content;
    }
  }
}
