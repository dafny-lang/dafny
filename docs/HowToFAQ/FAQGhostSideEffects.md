---
title: How can ghost code call methods with side effects?
---

## Question

How can ghost code call methods with side effects?

## Answer

Ghost code may not have any effect on non-ghost state, but ghost code can have effects on ghost state.
So a ghost method may modify ghost fields, as long as the specifications list the appropriate fields in
the appropriate modifies clauses. The example code below demonstrates this:

```dafny
  class C {
    ghost var c: int

    ghost method m(k: int)
      modifies this
      ensures c == k
    { 
      c := k;
    }

    ghost method p() {
      var cc := new C;
      cc.m(8);
      assert cc.c == 8;
    }
  }
```
