---
title: Is there a way to write `if foo().equals(bar()) { x } else { y }` where `foo` and `bar` are methods?
---

## Question

Is there a way to write `if foo().equals(bar()) { x } else { y }` where `foo` and `bar` are methods?

## Answer

No. Methods have side-effects and so Dafny does not allow them in expressions.
So you need to call each method in a statement of its own, using temporary local variables to record the results,
and then formulate your expression.

If the methods in question do not have side-effects, they can be rewritten as functions or 'function by method'
and then the syntax decribed above is fine.
