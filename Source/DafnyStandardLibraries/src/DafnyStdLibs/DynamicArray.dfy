include "/Users/rwillems/SourceCode/dafny2/Source/DafnyStandardLibraries/src/DafnyStdLibs/BoundedInts.dfy"

module DafnyStdLibs.DynamicArray {
  import B = BoundedInts
  import opened BoundedInts
  import opened Wrappers

  export 
    reveals DynamicArray
    provides 
      DynamicArray.MAX_CAPACITY,
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

    const defaultValue: A
    var size: uint32
    var capacity: uint32
    var data: array<A>

    const MAX_CAPACITY: uint32 := (TWO_TO_THE_32 - 1) as uint32
    const MAX_CAPACITY_BEFORE_DOUBLING: uint32 := MAX_CAPACITY / 2

    ghost predicate Valid?()
      reads this, Repr
      ensures Valid?() ==> this in Repr
    {
      && Repr == {this, data}
      && capacity != 0
      && data.Length == capacity as int
      && size <= capacity
      && size as int == |items|
      && items == data[..size]
    }

    constructor(defaultValue: A, initialCapacity: uint32 := 8)
      requires initialCapacity > 0
      ensures size == 0
      ensures items == []
      ensures fresh(Repr)
      ensures Valid?()
      ensures capacity == initialCapacity
    {
      this.defaultValue := defaultValue;
      items := [];
      size := 0;
      capacity := initialCapacity;
      data := new A[initialCapacity](_ => defaultValue);
      Repr := {this, data};
    }

    /**
    Retrieve the element at index 
     */
    function At(index: uint32) : (element: A)
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
    method Put(index: uint32, element: A)
      requires index < size
      requires Valid?()
      modifies Repr, `items
      ensures Valid?()
      ensures items == old(items)[index := element]
    {
      data[index] := element;
      items := items[index := element];
    }

    /**
    Ensure that at least a reserved amount of elements can still be pushed onto the array in constant time

    Returns false only if it was not at all possible to provide the ensurance.
     */
    method Ensure(reserved: uint32) returns (s: bool)
      requires Valid?()
      ensures Valid?()
      modifies `capacity, Repr
      ensures s <==> reserved <= MAX_CAPACITY - size
      ensures s ==> reserved <= capacity - size
    {
      if reserved > MAX_CAPACITY - size {
        return false;
      }
      if reserved <= capacity - size {
        return true;
      }
      var newCapacity := capacity;
      while reserved > newCapacity - size
        decreases MAX_CAPACITY - newCapacity
        invariant newCapacity >= capacity
      {
        newCapacity := DefaultNewCapacity(newCapacity);
      }
      Realloc(newCapacity);
      return true;
    }

    /**
    Pop an element from the array in constant time
     */
    method PopFast()
      requires Valid?()
      requires size > 0
      modifies `size, `items
      ensures Valid?()
      ensures size == old(size) - 1
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
      modifies Repr, `size, `items
      ensures Valid?()
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
    method Push(element: A) returns (s: bool)
      requires Valid?()
      modifies Repr
      ensures Valid?()
      ensures s == (old(size) < MAX_CAPACITY)
      ensures !s ==>
                && unchanged(this)
                // && unchanged(items)
      ensures s ==>
                && size == old(size) + 1
                && items == old(items) + [element]
                && capacity >= old(capacity)
                // && if old(size == capacity) then fresh(data) else unchanged(`data)
    {
      if size == capacity {
        var d := ReallocDefault();
        if !d { return d; }
      }
      PushFast(element);
      return true;
    }

    method Realloc(newCapacity: uint32)
      requires Valid?()
      requires newCapacity > capacity
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

    function DefaultNewCapacity(capacity: uint32) : uint32 {
      if capacity < MAX_CAPACITY_BEFORE_DOUBLING
      then 2 * capacity
      else MAX_CAPACITY
    }

    method ReallocDefault() returns (s: bool)
      requires Valid?()
      modifies `capacity, `data, `Repr, data
      ensures Valid?()
      ensures !s <==> old(capacity) == MAX_CAPACITY
      ensures !s ==>
                && unchanged(this)
                && unchanged(data)
      ensures s ==>
                && fresh(data)
                && old(capacity) < MAX_CAPACITY
                && capacity == old(if capacity < MAX_CAPACITY_BEFORE_DOUBLING
                                   then 2 * capacity else MAX_CAPACITY)

    {
      if capacity == MAX_CAPACITY {
        return false;
      }
      Realloc(DefaultNewCapacity(capacity));
      return true;
    }

    /**
    For internal use
     */
    method CopyFrom(newData: array<A>, count: uint32)
      requires count as int <= newData.Length
      requires count <= capacity
      requires data.Length == capacity as int
      modifies data
      ensures data[..count] == newData[..count]
      ensures data[count..] == old(data[count..])
    {
      for idx: uint32 := 0 to count
        invariant idx <= capacity
        invariant data.Length == capacity as int
        invariant data[..idx] == newData[..idx]
        invariant data[count..] == old(data[count..])
      {
        data[idx] := newData[idx];
      }
    }
  }
}