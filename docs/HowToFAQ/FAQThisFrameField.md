---
title: How do I say 'reads if x then this\`y else this\`z'? Dafny complains about the 'this'.
---

## Question: 

How do I say 'reads if x then this\`y else this\`z'? Dafny complains about the 'this'.

## Answer:

Here is some sample code that show a workaround.

```dafny
trait Test {
  var y: int
  var z: int
  predicate readsY() reads this`y { true }
  predicate readsZ() reads this`z { true }
  function {:opaque} MyFunc(x: bool): int
    reads if x then readsY.reads() else readsZ.reads() {
    if x then y else z
  }
}

```