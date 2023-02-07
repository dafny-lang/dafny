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
  function {:opaque} MyFunc(x: bool): int
    reads (if x then {this} else {})`y, (if x then {} else {this})`z {
    if x then y else z
  }
}

```