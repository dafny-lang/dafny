---
title: What is the difference between a type and a newtype?
---
## Question

One can define a _subset type_ like this
```
type int8 = x: int | -128 <= x < 128
```
and a newtype like this
```
newtype nint8 = x | -128 <= x < 128
```

What is the difference?

## Answer

In both cases, the values in the type are limited to the given range,
but a _newtype_ intends to define a whole new type that, although still based on integers and allowing integer operations,
is not intended to be mixed with integers.

This is evident in the allowed conversions, as shown in this example code:
```
{% include_relative FAQNewtype.dfy %}
```

The other important characteristic of `newtype`s is that they may have a different representation in the compilation target language.
Subset types are always represented in the same way as the base type.  But a newtype may use a different representation.
For example, the newtype defined above might use a `byte` representation in Java, whereas an `int` is a `BigInteger`.
The representation of a newtype can be set by the program author using the [`{:nativeType}`](../DafnyRef/DafnyRef#sec-nativetype) attribute.
