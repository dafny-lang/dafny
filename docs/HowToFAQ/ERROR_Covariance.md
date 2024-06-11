---
title: "Error: value does not satisfy subset constraints of T"
---

The error "value does not satisfy subset constraints of T"
for some type name `T` arises when a value is trying to be converted to a subset type `T`,
and the value cannot be proved to satisfy the predicate that defines the subset type.

This is pretty clear when one is trying to assign, say an `int` to a `nat`, but is more complex when using generic types.

This example
```dafny
{% include_relative ERROR_Covariance.dfy %}
```
produces
```text
{% include_relative ERROR_Covariance.txt %}
```

The problem is that the code is trying to convert a `formula<neg>` to a `formula<real>`.
While a `neg` is a subtype of `real`, that does not imply a subtype relationship between
`formula<neg>` and `formula<real>`.
That relationship must be declared in the definition of `formula`.
By default, the definition of a generic type is _non-variant_, meaning there is no
subtype relationship between `formula<T>` and `formula<U>` when `T` is a subtype of `U`.
What is wanted here is for `formula` to be _covariant_, so that
`formula<T>` is a subtype of `formula<U>` when `T` is a subtype of `U`.
For that, use the declaration `formula<+T>`.

To declare `formula` as _contravariant_ use `formula<-T>`. Then `formula<U>` is a subtype of `formula<T>` when `T` is a subtype of `U`.

Type parameter characteristics are discussed in [the reference manual](../DafnyRef/DafnyRef.html#sec-type-parameter-variance)
