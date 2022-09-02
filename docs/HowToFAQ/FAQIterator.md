---
title: How do I create and use an iterator?
---

## Question

How do I create and use an iterator?

## Answer

Here is an example of an iterator:
```dafny
iterator Gen(start: int) yields (x: int)
  yield ensures |xs| <= 10 && x == start + |xs| - 1
{
  var i := 0;
  while i < 10 invariant |xs| == i {
    x := start + i;
    yield;
    i := i + 1;
  }
}
```
An instance of this iterator is created using
```dafny
iter := new Gen(30);
```
It is used like this:
```
method Main() {
  var i := new Gen(30);
  while true
    invariant i.Valid() && fresh(i._new)
    decreases 10 - |i.xs|
  {
    var m := i.MoveNext();
    if (!m) {break; }
    print i.x;
  }
}
```
Here the method `MoveNext` and the field `xs` (and others) are automatically created, 
as decribed in the [reference manual](../DafnyRef/DafnyRef#sec-iterator-types).

Note that the syntax of iterators is under discussion in the Dafny development team and may change or have additional alternatives in the future.
