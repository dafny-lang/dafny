---
title: What is the difference between a lemma and a ghost method?
---

## Question

What is the difference between a lemma and a ghost method?

## Answer

A `lemma` is a `ghost method` that does not have a `modifies` clause. Lemmas also do not typically return results.
However, in most places where a lemma is used, it must be declared as a lemma. For example the lemma call that can be part of an expression must call a method that is declared to be a lemma, not a ghost method.

A lemma may also be called as a statement in the body of a method, but here a ghost method is allowed as well, so either can be used.
