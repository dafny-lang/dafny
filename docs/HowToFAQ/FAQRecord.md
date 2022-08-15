---
title: How does one define a record?
---

## Question

How does one define a record?

## Answer

The Dafny `datatype` feature lets you define simple or complex records, including recursive ones.

A simple record might be defined as
```dafny
datatype ABCD = A | B | C | D
```
Variables of type `ABCD` can take one of the four given values.

The record alternatives can also hold data:
```dafny
datatype ABCD = A(i: int) | B(s: string) | C(r: real) | D
const a: ABCD := A(7)
const b: ABCD := B("asd")
const c: ABCD := C(0.0)
const d: ABCD := D
```

You can determine which alternative a record value is with the built-in test functions: with the definitions above, `a.A?` is true and `b.C?` is false. And you can extract the record alternative's
data: in the above `a.i` is well-defined if `a.A?` is true, in which case it has the value `7`.

There is more description of datatypes [here](https://dafny.org/dafny/DafnyRef/DafnyRef#sec-algebraic-datatype).
