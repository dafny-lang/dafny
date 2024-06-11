---
title: Is there any difference between a method without a modifies clause and a function with a reads this clause?  I know that the latter you can use in expressions, but otherwise, is there anything the former can do that the latter can’t, for example?
---

## Question

Is there any difference between a method without a `modifies` clause and a function method with a `reads this` clause?  I know that the latter you can use in expressions.  Is there anything the former can do that the latter can’t, for example?

## Answer

Compared to a function, a method can
- allocate objects and arrays (`new`)
- use non-determinism
- use loops
- have multiple outputs
- read anything in the heap
