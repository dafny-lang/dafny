---
title: "What does `forall v :: v in vals ==> false` evaluate to if `vals` is non-empty?"
---

## Question

What does `forall v :: v in vals ==> false` evaluate to if `vals` is non-empty?
Should it be false? I’m having some problem proving the last assertion in Dafny.

```dafny
assert vals != [];
assert MatchingResult() == (forall v :: v in vals ==> false);
assert !MatchingResult();
```

## Answer

The problem here is the trigger on the quantification expression.
Dafny sees the `forall` quantifier but uses it only when there is a `v in vals` fact in the context for some v (this is what the annotation on the forall in the VSCode IDE means: Selected triggers: {v in vals}).  So until you give it a concrete fact to "trigger" on, it doesn't use your quantifier.

It is not recommended that users insert triggers in their Dafny code. Rather, it is better to reorganize the 
quantification expressions to make the desired trigger more obvious to the Dafny tool.
Here are two references that explain triggers in more detail:
- [A wiki page on triggers](https://github.com/dafny-lang/dafny/wiki/FAQ#how-does-dafny-handle-quantifiers-ive-heard-about-triggers-what-are-those)
- [Pages 2--4 of this paper](https://pit-claudel.fr/clement/papers/dafny-trigger-selection-CAV16.pdf)
