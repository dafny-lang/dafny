---
title: When a lemma has multiple ensures clauses, I’m finding that they interact, when I expected them to be independent.  For example, commenting out one of them can make another one not verify.  How should I think about this?
---

## Question

When a lemma has multiple ensures clauses, I’m finding that they interact, when I expected them to be independent.  For example, commenting out one of them can make another one not verify.  How should I think about this?

## Answer

Multiple ensures clauses, such as `ensures P ensures Q ensures R` is equivalent to the conjunction, in order, of the ensures predicates: `ensures P && Q && R`.
The order is important if an earlier predicate is needed to be sure that a later one is well defined. For example,
if `a` is an `array?`, the two predicates in `ensures a != null ensures a.Length > 0`
must be in that order because `a.Length` is well-defined only if `a != null`.

In addition, sometimes one ensures clause serves as an intermediate reasoning step for the next one. Without the earlier clause, Dafny can have trouble proving the second one, even though it is valid.
With the first predicate as an intermediate step, the second is then more easily proved.

This order dependence of postconditions is also the case for preconditions and loop invariants
