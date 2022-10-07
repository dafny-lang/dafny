---
title: Is there a way to use methods within expressions?
---

## Question

Is there a way to use methods within expressions?

## Answer

No. Dafny distinguishes statements and expressions. Statements are permitted to update variables and fields (that is, have side-effects); expressions are not allowed to do so. In general, methods may have side-effects and so Dafny does not allow methods in expressions.
So you need to call each method in a statement of its own, using temporary local variables to record the results,
and then formulate your expression.

If the methods in question do not have side-effects, they can be rewritten as functions or 'function by method'
and then the syntax decribed above is fine.
