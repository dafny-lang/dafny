include "/Users/rwillems/SourceCode/dafny2/Source/DafnyStandardLibraries/src/DafnyStdLibs/BoundedInts.dfy"
include "/Users/rwillems/SourceCode/dafny2/Source/DafnyStandardLibraries/src/DafnyStdLibs/DynamicArray.dfy"

module DynamicArrayExamples {
  import opened DafnyStdLibs.DynamicArray
  import opened DafnyStdLibs.BoundedInts

  method {:test} InitialCapacity() {
    var arr := new DynamicArray<int>(0, 101);
    for i: int := 0 to 100
      invariant fresh(arr.Repr)
      invariant arr.Valid?()
      invariant arr.size as int == i
      invariant arr.capacity == 101
    {
      arr.PushFast(i);
    }
  }

  method {:test} Ensure() {
    var arr := new DynamicArray<int>(0);
    assert arr.size == 0;
    var s := arr.Ensure(101 as uint32);
    assert s;
    assert arr.capacity >= 101;
    assert arr.size == 0;
    for i: int := 0 to 100
      invariant fresh(arr.Repr)
      invariant arr.Valid?()
      invariant arr.size as int == i
      invariant arr.capacity >= 101
    {
      arr.PushFast(i);
    }
  }

  method {:test} Push_At_Put_PopFast_PushFast() {
    var arr := new DynamicArray<int>(0);
    for i: int := 0 to 1000
      invariant arr.Valid?()
      invariant fresh(arr.Repr)
      invariant arr.size as int == i
    {
      assert arr.size as int == i;
      var r := arr.Push(i);
      assert r;
      assert arr.size as int == i + 1;
    }

    expect arr.At(30) == 30;
    arr.Put(30, 31);
    expect arr.At(30) == 31;

    arr.PopFast();
    arr.PopFast();
    arr.PushFast(3);
    arr.PushFast(4);
  }
}