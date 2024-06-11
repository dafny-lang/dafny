---
title: Why do I need a witness clause when I define a subset type or newtype?
---

## Question

Why do I need a witness clause in subtype definitions like
```
type A = s: int | Prime(x) witness 13
```

## Answer

Dafny generally assumes that types are non-empty; the witness is an example value that is in the type, demonstrating that the type is non-empty.

There are defaults for the `witness` clause, so you don't always have to have one. The default value is some zero-equivalent value: `0` for `int` based types, `0.0` for `real`-based types, 
empty sets, sequence and maps for those base types.

And, it is permitted to have possibly empty types by using a witness clause `witness *`, but there are restrictions on the use of possibly empty types.
For instance, a declaration of a variable with a possibly-empty type will need an initializer,
if that variable is ever used, because Dafny requires variables to be 'definitely assigned' before being used.

The Reference Manual contains a [discussion about witness clauses](../DafnyRef/DafnyRef#sec-witness-clauses).
