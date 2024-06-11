---
title: When proving an iff (<==>), is there a nice way to prove this by proving each side of the implication separately without making 2 different lemmas?
---

## Question

When proving an iff (<==>), is there a nice way to prove this by proving each side of the implication separately without making 2 different lemmas?

## Answer

Here are two ways to prove `A <==> B`:

```
if A {
  // prove B...
}
if B {
  // prove A...
}
```
Another way is
```
calc {
  A;
==
  // ...
==
  B;
}
```
