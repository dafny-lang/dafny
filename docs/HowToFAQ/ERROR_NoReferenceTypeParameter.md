---
title: "Error: type parameter 0 (K) passed to type A must support no references"
---

Ordinarily, a type parameter `X` can be instantiated with any type.

However, in some cases, it is desirable to say that `X` is only allowed to be instantiated by types that have certain characteristics. One such characteristic is that the type does not have any references.

A “reference”, here, refers to a type that is or contains a reference type. Reference types are class and trait types. So, if a type parameter is restricted to only “no reference” types, then you cannot instantiate it with a class type or a trait type.
A datatype can also include a reference. For example,
datatype MyDatatype = Ctor(x: MyClass)
More subtly, a type
datatype D<X> = Ctor(x: X)
might also contain a reference type if `X` is a type that can contain a reference type.


If you’re getting the “no reference” error, then you’re either trying to write an unbounded quantifier over a type that may contain references, or you’re trying to use a type that may contain references to instantiate a type parameter restricted to no-reference types.
Type characteristics that a type parameter must satisfy are written in parentheses after the type name and are separated by commas. For example, to say that a type parameter `X` must not contain any references, you would declare it as `X(!new)`. To further ensure it supports compile-time equality, you would declare it as `X(!new,==)`.
Presumably, you’re trying to instantiate a type parameter like `X(!new)` with a type that may contain references.

There is more discussion of type parameter characteristics in the [reference manual](../../DafnyRef/DafnyRef#sec-type-parameters).
