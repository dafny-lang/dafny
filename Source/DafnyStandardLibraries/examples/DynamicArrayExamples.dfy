module DynamicArrayExamples {
  import opened Std.DynamicArray
  import opened Std.BoundedInts

  @Test
  method Ensure() {
    var arr := new DynamicArray<int>();
    arr.Ensure(100, 3);
    for i: int := 0 to 100
      invariant fresh(arr.Repr)
      invariant arr.Valid?()
      invariant arr.size as int == i
      invariant arr.capacity >= 100
    {
      arr.PushFast(i);
    }
  }

  @Test
  method Push_At_Put_PopFast_PushFast() {
    var arr := new DynamicArray<int>();
    for i: int := 0 to 1000
      invariant arr.Valid?()
      invariant fresh(arr.Repr)
      invariant arr.size as int == i
    {
      arr.Push(i);
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