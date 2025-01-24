module Std.DynamicArray {
  import opened BoundedInts
  import opened Wrappers

  export
    reveals DynamicArray
    provides
      BoundedInts,
      DynamicArray.items,
      DynamicArray.capacity,
      DynamicArray.Repr,
      DynamicArray.Valid?,
      DynamicArray.size,
      DynamicArray.At,
      DynamicArray.Put,
      DynamicArray.Push,
      DynamicArray.PushFast,
      DynamicArray.PopFast,
      DynamicArray.Ensure

  /**
  The `DynamicArray` module and class define a data structure that has the same performance characteristics of an array, 
  but additionally allows growing and shrinking the size of the array. The cost of shrinking the array is constant time, 
  while the cost of growing it by a single element is either constant time or linear in the size of the array. 
  When growing the array multiple times, the amortized cost of growing the array by one element is constant time.

  The downsize of using a DynamicArray is that it occupies up to twice the amount of memory as its size, 
  and when elements are removed, its occupied memory does not decrease. 
  */
  class DynamicArray<A> {
    ghost var items: seq<A>
    ghost var Repr: set<object>

    var size: nat
    var capacity: nat
    var data: array<A>

    ghost predicate Valid?()
      reads this, Repr
    {
      && Repr == {this, data}
      && data.Length == capacity as int
      && size <= capacity
      && size as int == |items|
      && items == data[..size]
    }

    constructor()
      ensures size == 0
      ensures items == []
      ensures fresh(Repr)
      ensures capacity == 0
      ensures Valid?()
    {
      items := [];
      size := 0;
      capacity := 0;
      data := new A[0];
      Repr := {this, data};
    }

    /**
    Retrieve the element at index 
     */
    function At(index: nat) : (element: A)
      reads this, Repr
      requires index < size
      requires Valid?()
      ensures element == items[index]
    {
      data[index]
    }

    /**
    Put element in the array at index 
     */
    method Put(index: nat, element: A)
      requires index < size
      requires Valid?()
      reads this, Repr
      modifies Repr, `items
      ensures Valid?()
      ensures fresh(Repr - old(Repr))
      ensures size == old(size)
      ensures items == old(items)[index := element]
    {
      data[index] := element;
      items := items[index := element];
    }

    /**
    Ensure that at least a reserved amount of elements can still be pushed onto the array in constant time

    Returns false only if it was not at all possible to provide the ensurance.
     */
    method Ensure(reserved: nat, defaultValue: A)
      requires Valid?()
      ensures Valid?()
      reads this, Repr
      modifies Repr
      ensures size == old(size)
      ensures items == old(items)
      ensures fresh(Repr - old(Repr))
      ensures reserved <= capacity - size
    {
      var newCapacity := capacity;
      while reserved > newCapacity - size
        invariant newCapacity >= capacity
      {
        newCapacity := DefaultNewCapacity(newCapacity);
      }
      if (newCapacity > capacity) {
        Realloc(defaultValue, newCapacity);
      }
    }

    /**
    Pop an element from the array in constant time
     */
    method PopFast()
      requires Valid?()
      requires size > 0
      modifies `size, `items
      ensures Valid?()
      ensures size < capacity
      ensures size == old(size) - 1
      ensures capacity == old(capacity)
      ensures items == old(items[..|items| - 1])
    {
      size := size - 1;
      items := items[..|items| - 1];
    }

    /**
    Push an element onto the array in constant time
     */
    method PushFast(element: A)
      requires Valid?()
      requires size < capacity
      reads this, Repr
      modifies Repr
      ensures Valid?()
      ensures fresh(Repr - old(Repr))
      ensures size == old(size) + 1
      ensures capacity == old(capacity)
      ensures items == old(items) + [element]
    {
      data[size] := element;
      size := size + 1;
      items := items + [element];
    }

    /**
    Push an element onto the array in constant time if there is available capacity, 
    and otherwise in time linear to the current size of the array.

    Returns false only if it was not at all possible to push the element onto the array.
     */
    method Push(element: A)
      requires Valid?()
      reads this, Repr
      modifies Repr
      ensures Valid?()
      ensures fresh(Repr - old(Repr))
      ensures size == old(size) + 1
      ensures items == old(items) + [element]
      ensures capacity >= old(capacity)
    {
      if size == capacity {
        ReallocDefault(element);
      }
      PushFast(element);
    }

    method Realloc(defaultValue: A, newCapacity: nat)
      requires Valid?()
      requires newCapacity > capacity
      reads this, Repr
      modifies `capacity, `data, `Repr, data
      ensures Valid?()
      ensures capacity == newCapacity
      ensures fresh(data)
    {
      var oldData, oldCapacity := data, capacity;
      data, capacity := new A[newCapacity](_ => defaultValue), newCapacity;
      CopyFrom(oldData, oldCapacity);
      Repr := {this, data};
    }

    function DefaultNewCapacity(capacity: nat): nat {
      if capacity == 0 then 8
      else 2 * capacity
    }

    method ReallocDefault(defaultValue: A)
      requires Valid?()
      reads this, Repr
      modifies `capacity, `data, `Repr, data
      ensures Valid?()
      ensures fresh(data)
      ensures capacity == old(DefaultNewCapacity(capacity))

    {
      Realloc(defaultValue, DefaultNewCapacity(capacity));
    }

    method CopyFrom(newData: array<A>, count: nat)
      requires count as int <= newData.Length
      requires count <= capacity
      requires data.Length == capacity as int
      reads this, Repr, data, newData
      modifies data
      ensures data[..count] == newData[..count]
      ensures data[count..] == old(data[count..])
    {
      forall index | 0 <= index < count
      {
        data[index] := newData[index];
      }
    }
  }
}