---
title: Is it possible to restrict a type parameter to be a reference type? I see you can use T(!new) but I’m looking for the opposite.
---

## Question

Is it possible to restrict a type parameter to be a reference type? I see you can use `T(!new)` but I’m looking for the opposite.

## Answer

No. The only restrictions available (as of version 3.7.3) are
- `T(==)` - type supports equality
- `T(0)` - type is auto-initializable
- `T(00)` - type is non-empty
- `T(!new)` - type may **not** be a reference type or contain a reference type

See the [appropriate section of the reference manual](../DafnyRef/DafnyRef#sec-type-parameter-variance) for more information.
