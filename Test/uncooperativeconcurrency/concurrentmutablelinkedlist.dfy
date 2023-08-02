trait HasOwner {
  ghost const owner: object?

  // Axiom in boogie that states that
  // modifylocked(this.owner) ==> modifyLocked(this)
  // readLocked(this.owner) ==> readLocked(this)
}

method Test<A>(m: MutableLinkedList<A>, a: A)
  modifies m, m.Repr // assumed at call site if class is separated
  requires m.Valid() // assumed at call site if class is separated
{
  m.insertElemAt(0, a);
}

class MutableLinkedList<A>
  extends HasOwner              // OWNER:
{
  var head: Node?<A>
  ghost var Repr: set<object>
  var size: int
  constructor(ghost owner: object?)
  ensures Valid()
    ensures this.owner == owner
  {
    head := null;
    Repr := {this};
    size := 0;
    this.owner := owner;
  }
  ghost predicate Valid()
    reads this, Repr  
  {
    && this in Repr
    && (forall t: HasOwner :: t in {this} + Repr ==> t == this || t.owner == this)
    && ((head == null && size == 0) ||
        ( && head in Repr
          && head.owner == this             // OWNER:
          && head.Repr == Repr - {this}
          && head.size == size
          && head.Valid()))
  }

  function elemAt(index: nat): A
    reads this, Repr
    requires Valid()
    requires index < size
  {
    // OWNER(auto):
    assert head.owner == this ||
      (if this.owner != null then head as object == this else head.owner == null);
    head.elemAt(index)
  }

   method replaceElemAt(index: nat, newElem: A)
    modifies Repr
    requires Valid()
    ensures Repr == old(Repr)
    ensures Valid()
    requires index < size
  {
    assert head.owner == this ||
      (if this.owner != null then head as object == this else head.owner == null);              // OWNER (auto):
    head.replaceElemAt(index, newElem);
  }

  method insertElemAt(index: nat, newElem: A)
    requires Valid()
    requires index <= size // Need to be waited for
    modifies Repr
    ensures Valid()
    ensures size == old(size) + 1
  {
    if head == null {
      head := new Node<A>(this, newElem, null);
      size := 1;
    } else {
      ghost var dummy;
      assert head.owner == this ||
      (if this.owner != null then head as object == this else head.owner == null);      // OWNER (auto): 
      head, dummy := head.insertElemAt(index, newElem);
      size := size + 1;
    }
    Repr := {this} + head.Repr;
  }

  method deleteElemAt(index: nat) returns (a: A)
    requires Valid()      // Can be assumed only if trying to acquire a lock
    requires index < size // Need to be waited for and tested
    modifies Repr
    ensures Valid()
    ensures size == old(size) - 1 // Useless at call site unless lock was acquire before
    ensures a == old(elemAt(index))
  {
    assert head.owner == this ||
      (if this.owner != null then head as object == this else head.owner == null);     // OWNER (auto): 
    head, a := head.deleteElemAt(index);
    size := size - 1;
    Repr := if head == null then {this} else {this} + head.Repr;
  }
}

class Node<A> extends HasOwner {
  var value: A
  var next: Node?<A>
  var size: nat
  ghost var Repr: set<object>

  constructor(ghost owner: object?, a: A, next: Node?<A>) ensures Valid()
    requires next != null ==> next.Valid() && next.owner == owner
    ensures this.next == next
    ensures this.value == a
    ensures next != null ==> next.Repr == Repr - {this}
    ensures this.owner == owner
  {
    this.value := a;
    this.next := next;
    this.Repr := if next == null then {this} else {this} + next.Repr;
    this.size := if next == null then 1 else next.size + 1;
    this.owner := owner;
    new;
  }

  ghost predicate Valid()
    reads this, Repr
    decreases |Repr|
  {
    && 1 <= |Repr|
    && this in Repr
    && size == |Repr|
    && (forall n: HasOwner <- Repr :: n.owner == owner)  // OWNER:
    && (if next == null then Repr == {this}
        else
          && next in Repr
          && next.Repr == Repr - {this}
          && next.Valid())
  }

  function elemAt(index: nat): A
    reads this, Repr
    decreases |Repr|
    requires Valid()
    requires index < size
  {
    if index == 0 then value else next.elemAt(index - 1)
  }

  method replaceElemAt(index: nat, newElem: A)
    modifies Repr
    requires Valid()
    ensures Repr == old(Repr)
    ensures Valid()
    ensures old(this.owner) == this.owner     // OWNER: 
    requires index < size
  {
    if index == 0 {
      this.value := newElem;
    } else {
      assert next == this || next.owner == this || next.owner == this.owner;      // OWNER (auto): 
      next.replaceElemAt(index - 1, newElem);
    }
  }

  method insertElemAt(index: nat, newElem: A)
    returns (m: Node<A>, ghost insertedElem: Node<A>)
    requires Valid()
    requires index <= size
    modifies Repr
    ensures if index > 0 then m == this else m.next == this && m == insertedElem
    ensures Valid()
    ensures m.Valid()
    ensures m.owner == this.owner                // OWNER: 
    ensures m.size == old(size) + 1
    ensures fresh(insertedElem)
    ensures m.Repr == old(Repr) + {insertedElem}
    ensures insertedElem.owner == this.owner
  {
    if index == 0 {
      m := new Node<A>(this.owner, newElem, this); // OWNER: 
      insertedElem := m;
      return;
    }
    var newNext;
    if index == 1 && next == null { // Insertion at the end
      newNext := new Node<A>(this.owner, newElem, null);
      insertedElem := newNext;
    } else {
      assert next == this || next.owner == this || next.owner == this.owner;     // OWNER (auto): 
      newNext, insertedElem := next.insertElemAt(index - 1, newElem);
    }
    this.next := newNext;
    Repr := {this} + newNext.Repr;
    size := size + 1;
    m := this;
  }

  method deleteElemAt(index: nat)
    returns (m: Node?<A>, deleted: A)
    requires Valid()
    requires index < size
    modifies Repr
    ensures if old(size) > 1 then m != null && m.size == old(size - 1) else m == null
    ensures deleted == old(elemAt(index))
    ensures m != null ==>
      && m.Repr < old(Repr)
      && m.Valid()
      && m.owner == this.owner   // OWNER: 
  {
    if index == 0 {
      deleted := this.value;
      m := this.next;
      
      assert if size > 1 then m != null && m.size == old(size - 1) else m == null;
      assert m != null ==> m.Valid();
      return;
    }
    assert next == this || next.owner == this || next.owner == this.owner;     // OWNER (auto): 
    next, deleted := next.deleteElemAt(index - 1);
    size := size - 1;
    m := this;
    assert next != null ==> this !in next.Repr;
    Repr := if next == null then {this} else {this} + next.Repr;
    assert next != null ==> next.Repr == Repr - {this};
    assert if old(size) > 1 then m != null && m.size == old(size - 1) else m == null;
    assert m != null ==> m.Valid();
  }
}

















