---
title: How do I use `forall` statements and expressions in a lemma?
---

## Question

If I'm trying to prove a lemma in Dafny with a `forall` statement that needs help in the body (`{}`) of the lemma, how do I make an arbitrary variable in the body of the lemma to help prove the `forall` statement?

## Answer

Note that there is a difference between a `forall` expression, which is a universally quantified formula, and a `forall` statement, which is used to establish the truth of a universally quantified formula. To do what you want to do, write:
```dafny
lemma MyLemma()
  ensures forall s :: P(s) ==> Q(s)
{
  forall t | P(t)
    ensures Q(t)
  {
    // Here, t is in scope, and P(t) is assumed.
    // Your task here is to prove Q(t) for this particular t.
  }
  // Here, you get to assume "forall t :: P(t) ==> Q(t)"
}
```

The `forall` in the ensures is an expression and the `forall` in the body of the lemma is a statement.

This use of the `forall` statement is what logicians call “universal introduction”.

Note the slight difference in syntax between the `forall` expression and `forall` statement.
Although Dafny tries to make the syntax of these sorts of things as similar as possible between expressions and statements, there are some differences. 
The following Dafny Power User note may be helpful in understanding the syntax: [Dafny Power User: Statement vs. Expression Syntax](http://leino.science/papers/krml266.html).
