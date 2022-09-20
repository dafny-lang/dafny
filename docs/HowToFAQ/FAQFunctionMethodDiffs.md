---
title: What is the difference between `function`, `method`, `function method`, and `function by method`?
---

## Question

What is the difference between `function`, `method`, `function method`, and `function by method`?

## Answer

The names of these alternatives will be changing between Dafny 3 and Dafny 4:

- `function` (`function method` in Dafny 3) -- is a non-ghost function
- `ghost function` (`function` in Dafny 3) -- is a ghost function
- _function by method_ can be either ghost or non-ghost and is a way of giving a method-like implementation for a function (cf. [the reference manual section on function declarations](../DafnyRef/DafnyRef#sec-function-declarations))
- `method` declares a non-ghost method
- `ghost method` declares a ghost method, though this is almost always done using a `lemma` instead

Note that
- Methods may have side effects but may not be used in expressions.
- Functions may be used in expressions but may not have side effects.
- Methods do not have reads clauses; functions typically do.
- Non-ghost methods and non-ghost functions may not be used in ghost code.
