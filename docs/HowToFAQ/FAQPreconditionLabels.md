---
title: How do labels in preconditions work?
---

## Question

How do labels in preconditions work?

## Answer

```dafny
{% include_relative FAQPreconditionLabels.dfy %}
```

In the code example above, the precondition `x == 0` is labeled with `Zero`.
Unlabeled preconditions are assumed at the beginning of a method body,
but labeled preconditions are not. Labeled preconditions are only assumed
when they are explicitly `reveal`ed. So in the example, the assert in method 
`M1` cannot be proved because the fact `x < 10` is not known. 
In method `M2`, that fact is made known by the `reveal` statement, and so here
the `assert` can be proved. The effect of the `reveal` is just as if an assumption were
made at the point of the `reveal` statement.

Note that if the `reveal` statement is in a `by`
block of an `assert by` statement, then the revealing is limited to the proof of the 
corresponding `assert`.

These same rules apply to labeled `assert` statements.

There is an expanded discussion in section 7 of [_Different Styles of Proofs_](http://leino.science/papers/krml276.html).
