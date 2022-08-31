---
title: What is `-` on bitvectors?
---

## Question

What is `-` on bitvectors?

## Answer

The `-` operator for bit-vectors is subtraction or unary negation.
Unary negation, `- b` is equivalent to `0 - b`.
This is not the same as complement, which is written as `! b`.

For example, the `bv5` value equivalent to the natural number `13` is `01101`.
- The complement of this value is `10010`, which is `18`.
- The negation of this value is `10011`, which is `19`.

In 2's complement fixed-bit-width arithmetic, `-x` is `!x + 1`.
