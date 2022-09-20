---
title: What is the difference between modifies this, modifies this.x, and modifies this`x?
---

## Question

What is the difference between `modifies this`, `modifies this.x`, and ``modifies this`x``?

## Answer

A `modifies` clause for a method lists object references whose fields may be modified by the body of the method.
- `this` means that all the fields of the `this` object may be modified by the body
- `this.x` (where `x` is a field of `this` and has some reference type) means that fields of `x` may be modified (but not the field `x` itself of `this`)
- ``this`x`` means that just the field `x` of `this` may be modified (and not any other fields, unless they are listed themselves)

If there are multiple items listed in the modifies clause, the implicit clause is the union of all of them.
More on framing (`modifies` and `reads` clauses) can be found in the [reference manual section on Framing specifications](../DafnyRef/DafnyRef#sec-frame-expression).
