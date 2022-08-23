---
title: Where do I put the reads clause in a subset type?
---

## Question:

This example
```dafny
{% include_relative FAQReadsClause.dfy %}
```
generates this error:
```text
{% include_relative FAQReadsClause.txt %}
```
but there is no obvious place to put a `reads` clause.

## Answer:

There is no place for the `reads` clause because no such clause should be needed.
A type definition is not allowed to depend on a mutable field;
the predicate in the subset type must be pure.

