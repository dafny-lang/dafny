---
title: Is there a way to do partial application for functions?
---

## Question

Is there a way to do partial application for functions in Dafny?

## Answer

Given
```
function f(i: int, j: int): int {...}
```
one can create a new partially-evaluated function, say evaluating the first argument at `2`, by writing the lambda expression `k => f(2,k)`.
But note that this does not do any evaluation, partial or not. It merely defines a new function `f'` of one argument, such at `f'(k)` is `f(2,k)`.

Dafny does not permit the syntax `f(2)` as a shorthand for `k => f(2,k)`.
