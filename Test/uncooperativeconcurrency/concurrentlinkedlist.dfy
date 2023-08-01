
include "separatedclass.dfy"

// Modified version of this datatype:
// https://github.com/aws/aws-cryptographic-material-providers-library-java/blob/main/AwsCryptographicMaterialProviders/dafny/AwsCryptographicMaterialProviders/src/CMCs/LocalCMC.dfy#L65
module ConcurrentDoublyLinkedList {

  import opened SeparatedClasses

  datatype Ref<T> =
    | Ptr(deref: T)
    | Null


  class ConcurrentDoublyLinkedList<T> extends OwnedObject {

    // New for the concurrent version
    ghost const inv: T -> bool
    
    var head: Ref<LinkedListNode<T>>
    var tail: Ref<LinkedListNode<T>>

    ghost var Items: seq<LinkedListNode<T>>

    constructor(ghost inv: T -> bool)
      ensures Invariant()
      ensures this.inv == inv
    {
      // Forced by being a separated class
      Owner := this;

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
      && forall v <- Items :: v.Owner == this
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

    method PushCell(toPush: LinkedListNode<T>)
      requires toPush !in Items
      requires toPush.next.Null? && toPush.prev.Null?
      // New for concurrent version
      requires toPush.Owner == this;
      requires Invariant()
      requires inv(toPush.value)
      modifies this, Items, toPush
      ensures Invariant()
    {
      Items := [toPush] + Items;

      var cRef := Ptr(toPush);
      if head.Ptr? {
        assert head.deref in Items;
        assert CanAccess(head.deref);
        head.deref.prev := cRef;
        toPush.next := head;
        head := cRef;
      } else {
        assert CanAccess(this);
        head := cRef;
        tail := head;
      }
    }

    method Push(value: T)
      requires Invariant()
      requires inv(value)
      modifies this, Items
      ensures Invariant()
    {
      var toPush := new LinkedListNode<T>(value);
      toPush.Owner := this;
      PushCell(toPush);
    }

    method {:vcs_split_on_every_assert} Remove(toRemove: LinkedListNode<T>)
      requires Invariant()
      requires toRemove in Items
      modifies this, Items
      ensures Invariant()
      ensures multiset(Items) == multiset(old(Items)) - multiset{toRemove}
      ensures toRemove !in Items
      ensures toRemove.next.Null? && toRemove.prev.Null?
      ensures toRemove.Owner == null
      ensures |Items| < |old(Items)|
    {
      ghost var pos := IndexOfNode(Items, toRemove);
      // This is s[..pos] + s[pos+1]
      // where pos :| s[pos] == c
      Items := RemoveNode(Items, toRemove);

      if toRemove.prev.Null? {
        // toRemove is head
        assert toRemove.prev.Null? ==> Ptr(toRemove) == head;
        assert pos == 0;
        head := toRemove.next;
      } else {
        // toRemove is !head
        assert toRemove != head.deref;
        assert 0 != pos;
        assert 0 < |Items|;
        assert Items[pos - 1] == toRemove.prev.deref;
        toRemove.prev.deref.next := toRemove.next;
      }

      if toRemove.next.Null? {
        // toRemove is tail
        assert toRemove.next.Null? ==> Ptr(toRemove) == tail;
        tail := toRemove.prev;
      } else {
        // toRemove is !tail
        assert toRemove != tail.deref;
        assert 0 < |Items|;
        toRemove.next.deref.prev := toRemove.prev;
      }

      label AFTER:

      assert {:split_here} true;
      assert Items == old@AFTER(Items);
      assert toRemove !in Items;

      toRemove.next := Null;
      toRemove.prev := Null;
      SetOwner(toRemove, null);
    }

    // TODO: seems like it should be a general Seq utility...
    ghost function {:opaque} RemoveNode(s: seq<LinkedListNode<T>>, v: LinkedListNode<T>): (s': seq<LinkedListNode<T>>)
      requires multiset(s)[v] == 1
      ensures v !in s'
      ensures multiset(s') == multiset(s) - multiset{v}
      ensures
        var pos := IndexOfNode(s, v);
        && (forall i: nat | 0 <= i < pos :: s[i] == s'[i])
        && (forall i: nat | pos <= i < |s'| :: s[i+1] == s'[i])
        && (s' == s[..pos] + s[pos+1..])
    {
      var pos := IndexOfNode(s, v);
      // Associativity, s[pos..] is the sum of both sides
      assert s == s[..pos] + s[pos..];
      // the 1 v MUST be in the right side
      assert multiset(s[pos..])[v] == 1;
      // Associativity, s[pos..] is the sum of both sides
      assert s[pos..] == [s[pos]] + s[pos+1..];
      s[..pos] + s[pos+1..]
    }

    ghost function IndexOfNode(s: seq<LinkedListNode<T>>, v: LinkedListNode<T>): (pos: nat)
      requires v in s
      ensures pos < |s| && s[pos] == v
      ensures v !in s[..pos]
    {
      if s[0] == v then 0 else 1 + IndexOfNode(s[1..], v)
    }

    // New for concurrent version
    method SplitBy(p: T -> bool) returns (matching: ConcurrentDoublyLinkedList<T>) 
      ensures Invariant()
      ensures matching.Invariant()
      ensures multiset(old(Items)) == multiset(Items) + multiset(matching.Items)
      ensures multiset(Items) !! multiset(matching.Items)
      ensures forall i | 0 <= i < |Items| :: !p(Items[i].value)
      ensures forall i | 0 <= i < |matching.Items| :: p(matching.Items[i].value)
      // TODO: Something about order too

    method FindBy(p: T -> bool) returns (result: LinkedListNode?<T>) 
      ensures result != null <==> exists item <- Items :: p(item.value)
      // TODO: Something about order too
   }

  class LinkedListNode<T> extends OwnedObject {
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

}

