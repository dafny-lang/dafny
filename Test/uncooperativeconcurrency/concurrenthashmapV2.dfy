class {:separated} ConcurrentHashMap {






}

function Hash<T>(t: T): nat

class {:separated} ConcurrentDoublyLinkedList<T(0)> {

  ghost const inv: T -> bool

  var head: Ref<LinkedListNode<T>>
  var tail: Ref<LinkedListNode<T>>

  ghost var Items: seq<LinkedListNode<T>>

  constructor(ghost inv: T -> bool) {
    this.inv := inv;
    head := Null;
    tail := Null;
    Items := [];
  }

  ghost predicate Invariant()
    reads this, Items
  {
    // head and tail properties
    && (0 == |Items| <==> head.Null? && tail.Null?)
    && (0 < |Items| <==>
        && head.Ptr?
        && tail.Ptr?
        && head.deref == Items[0]
        && tail.deref == Items[|Items| - 1])
    && (head.Ptr? <==> tail.Ptr?)
    && (head.Ptr? ==> head.deref.prev.Null?)
    && (tail.Ptr? ==> tail.deref.next.Null?)
        // Every Cell in the DoublyLinkedList MUST be unique.
        // Otherwise there would be loops in prev and next.
        // For a Cell at 4, next MUST point to 5 or Null?.
        // So if a Cell exists as 4 and 7
        // then it's next would need to point to _both_ 5 and 8.
    && (forall v <- Items :: multiset(Items)[v] == 1)
        // Proving order is easier by being more specific
        // and breaking up prev and next.
        // Order means Cell 4 point to 3 and 5
        // in prev and next respectively.
    && (forall i: nat | 0 <= i < |Items| ::
          && Prev?(i, Items[i], Items)
          && Next?(i, Items[i], Items)
        )
    // New for the concurrent version
    && forall v <- Items :: inv(v.value)
  }

  ghost predicate Prev?(i:nat, c: LinkedListNode<T>, Items' : seq<LinkedListNode<T>>)
    reads Items'
    requires 0 <= i < |Items'|
    requires Items'[i] == c
  {
    if i == 0 then
      Items'[0].prev.Null?
    else
      && Items'[i].prev.Ptr?
      && Items'[i].prev.deref == Items'[i - 1]
  }

  ghost predicate Next?(i:nat, c: LinkedListNode<T>, Items' : seq<LinkedListNode<T>>)
    reads Items'
    requires 0 <= i < |Items'|
    requires Items'[i] == c
  {
    if i < |Items'| -1 then
      && Items'[i].next.Ptr?
      && Items'[i].next.deref == Items'[i + 1]
    else
      assert i == |Items'| - 1;
      && Items'[i].next.Null?
  }

  method PushFront(t: T)
    requires Invariant()
    requires inv(t)
    modifies this, Items
    ensures Invariant()
  {
    var newNode := new LinkedListNode<T>(t);
    Items := [newNode] + Items;
    var cRef := Ptr(newNode);
    if head.Ptr? {
      head.deref.prev := cRef;
      newNode.next := head;
      head := cRef;
    } else {
      head := cRef;
      tail := head;
    }
  }
}

datatype Ref<T> =
  | Ptr(deref: T)
  | Null

class LinkedListNode<T> {
  var value: T
  var next: Ref<LinkedListNode<T>>
  var prev: Ref<LinkedListNode<T>>

  constructor(value: T) 
    ensures this.value == value
    ensures next == Null
    ensures prev == Null
  {
    this.value := value;
    next := Null;
    prev := Null;
  }
}

class {:separated} ConcurrentArray<T> {

  ghost const inv: T -> bool

  // TODO: This may need to be more like an Action<(), T> to
  // create the value if T is a reference type.
  // But it might be better to just use T? with null in that case instead.
  const default: T
  var storage: array<T>

  ghost var {:separatedHeap} Repr: set<object>

  ghost predicate Valid() 
    reads this, Repr
  {
    && this in Repr
    && storage in Repr
    && inv(default)
    && forall t <- storage[..] :: inv(t)
  }

  constructor(default: T, ghost inv: T -> bool) 
    requires inv(default)
  {
    this.default := default;
    this.storage := new T[10](i => default);
  }

  function Select(i: nat): (r: T)
    requires Valid()
    reads this, Repr
    ensures inv(r)
  {
    if i < storage.Length then
      storage[i]
    else
      default
  }

  method Update(i: nat, newValue: T) 
    requires Valid()
    modifies Repr
  {
    if storage.Length <= i {
      Resize(i + 1);
    }
    assert i < storage.Length;
    storage[i] := newValue;
  }

  method Resize(newCapacity: int)
    requires Valid()
    // TODO: accidentally got away with not writing Repr here,
    // but Valid() ==> this in Repr, so that should be legal still?
    modifies this
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures old(storage.Length) <= storage.Length
    ensures newCapacity <= storage.Length
  {
    if newCapacity <= storage.Length {
      return;
    }
    var newStorage := new T[newCapacity](i => default);
    // Ideally this could be compiled to an optimized array copy
    // (e.g. System.arraycopy in Java)
    forall i | 0 <= i < storage.Length {
      newStorage[i] := storage[i];
    }
    storage := newStorage;
    Repr := {this, storage};
  }
}