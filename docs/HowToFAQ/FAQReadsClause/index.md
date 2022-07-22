---
title: Where do I put the reads clause?
---

This example
```dafny
{% include-relative Example.dfy %}
```
generates this error:
```text
{% include-relative out.txt %}
```
but there is no obvious place to put a `reads` clause.

There is no place for the `reads` clause because no such clause should be needed.
A type definition is not allowed to depend on a mutable field;
the predicate in the subset type must be pure.

