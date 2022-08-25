---
title: What is the difference between `function`, `method`, `function method`, and `function by method`?
---

## Question

What is the difference between `function`, `method`, `function method`, and `function by method`?

## Answer

The names of these alternatives will be changing between Dafny 3 and Dafny 4:

- `function` (`function method` in Dafny 3) -- is a non-ghost function
- `ghost function` (`function` in Dafny 3) -- is a ghost function
- `function by method` declares a function that can be called from non-ghost contexts. Its body is a ghost expression that specifies what the function returns, and the `by method` body declares a non-ghost method implementation for the function (cf. [the reference manual section on function declarations](https://dafny.org/dafny/DafnyRef/DafnyRef#sec-function-declarations)).
- `method` or `ghost method` -- a method

Note that
- Methods may have side effects but may not be used in expressions
- Functions may be used in expressions but may not have side effects
- Methods do not have reads clauses; functions typically do
- Ghost methods and ghost functions may only be used in ghost code
