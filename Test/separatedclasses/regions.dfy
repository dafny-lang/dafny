// RUN: %baredafny verify %args --region-checks:true "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module RegionTests {
  // A node that, when attached to another, cannot be modified except by that other node

  class Node {
    //ghost var Region: object? // TODO: Remove once option set
    ghost var Repr: set<object>
    var value: int
    var next: Node?
    ghost predicate Invariant()
      reads this, Repr
    {
      && this in Repr
      && (if next == null then Repr == {this} else
          && next in Repr
          && this !in next.Repr
          && Repr == {this} + next.Repr
          && next.Region == this)
    }
    function GetValue(): int
      reads this
    {
      value
    }
    method Obtain() returns (v: int) {
      v := value;
    }
    method Increase() modifies this`value {
      value := value + 1;
    }

    constructor Wrong(value: int, next: Node?)
      modifies next
      requires next != null ==> next.Invariant() // && next.Region == null
      // Forgot to require the region of next to be null
      ensures next != null ==>
         && old(next.value) == next.value
         && old(next.next) == next.next
         && next.Region == this
      ensures Region == null && this.value == value && this.next == next
      ensures Invariant()
    {
      this.value := value;
      this.next := next;
      Region := null;
      Repr := if next == null then {this} else {this} + next.Repr;
      new;
      if next != null {
        next.Region := this;  // Error: could not prove that next.Region == this || next.Region == this.Region || (next.Region == null && fresh(next));
      }
    }

    constructor(value: int, next: Node?)
      modifies next
      requires next != null ==> next.Invariant() && next.Region == null
      ensures next != null ==>
         && old(next.value) == next.value
         && old(next.next) == next.next
         && next.Region == this
      ensures Region == null && this.value == value && this.next == next
      ensures Invariant()
    {
      this.value := value;
      this.next := next;
      Region := null;
      Repr := if next == null then {this} else {this} + next.Repr;
      new;
      if next != null {
        next.Region := this; // Ok because next.Region == this.Region at this point
      }
    }
    method ChangeNextValueWrong(newValue: int)
      requires next != null && next != this
      //requires next.Region == this // Oops forgot
      modifies next
      ensures next.next == old(next.next) && next.Region == old(next.Region)
      ensures next.value == newValue
    {
      next.value := newValue; // Error: could not prove next.Region == this.Region || next.Region == this || (next.Region == null && fresh(next))
    }
    method ChangeNextValue(newValue: int)
      requires next != null && next != this
      requires next.Region == this // Guaranteed by the invariant
      modifies next
      ensures next.next == old(next.next) && next.Region == old(next.Region)
      ensures next.value == newValue
    {
      next.value := newValue; // OK
    }
  }

  method Test() {
    var c := new Node(0, null);
    c.value := 2;            // OK
    var d := new Node(0, c); // At this point, c belongs to the region d
    assert c.Region == d;    // OK
    assert d.next == c;      // OK
    var x := c.value;        // OK even if not in the same region
    var y := c.GetValue();   // OK, it's only a function read
    var z := c.Obtain();     // OK, it's only a method without modifies clause
    if * {
      c.value := 3;          // Error: Cannot prove that c.Region == null
    } else {
      c.Increase();          // Error, cannot prove that c.Region == null
    }
  }

  method Test2() {
    var c := new Node(0, null);
    c.value := 2;            // OK
    var d := new Node(0, c); // After this, c belongs to the region d
    assert c.Region == d;    // OK
    assert d.next == c;
    d.ChangeNextValue(3);
    assert c.value == 3;     // OK
  }

  class ArrayWrapper {
    const elements: array<int>
    constructor()
      ensures elements.Region == this
      ensures fresh(elements)
      ensures elements.Length == 4
    {
      elements := new int[4];
      new;
      elements.Region := this;
    }
    method SetWrong(index: int, newValue: int) returns (previousValue: int)
      requires 0 <= index < elements.Length
      // requires elements.Region == this // If forgotten, error
    {
      previousValue := elements[index]; // OK, it's only a read
      elements[index] := newValue;  // Error: Cannot prove that elements.Region == this || elements.Region == this.Region || (fresh(elements) && elements.Region == null)
    }
    method Set(index: int, newValue: int) returns (previousValue: int)
      requires 0 <= index < elements.Length
      requires elements.Region == this
      ensures elements[index] == newValue
    {
      previousValue := elements[index]; // OK
      elements[index] := newValue;      // OK
    }
  }

  method Test3() {
    var c := new ArrayWrapper();
    var x := c.elements[0];       // OK
    if * {
      c.elements[0] := 3;         // Error: Cannot prove that c.elements.Region == null
    } else {
      var previousValue := c.Set(0, 3);                // OK
      assert c.elements[0] == 3;  // OK
    }
  }
}














