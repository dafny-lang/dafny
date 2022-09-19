---
title: How do I pattern match against a head and tail of a sequence or against a set?
---

## Question

How do I pattern match against a head and tail of a sequence or against a set?

## Answer

You can't. Match [expressions](https://dafny.org/dafny/DafnyRef/DafnyRef#sec-match-expression) and [statements](https://dafny.org/dafny/DafnyRef/DafnyRef#sec-match-statement) operate on `datatype` values and not on other Dafny types like sets, sequences, and maps. If statements, perhaps with [binding guards](https://dafny.org/dafny/DafnyRef/DafnyRef#sec-binding-guards), may be an alternative.

