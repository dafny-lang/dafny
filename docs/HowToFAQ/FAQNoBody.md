---
title: "Is there a way to prevent 'Warning: note, this forall statement has no body' from occurring? I have a forall loop with no body that results in the lemma verifying, but if I add a body (even an empty body) the lemma doesn't verify."
---

## Question

Is there a way to prevent "Warning: note, this forall statement has no body" from occurring? I have a forall loop with no body that results in the lemma verifying, but if I add a body (even an empty body) the lemma doesn't verify.

## Answer

The Dafny verifier allows you to omit the body of various constructs. For example, if you write a method without a body, the verifier will gladly check calls to the method against that specification (after checking the well-formedness of the method specification). This is nice, because it lets you write the specification of a method and then start using it in other places, only to later return to filling in the body of the method.

The verifier is happy with such a body-less thing, but the once verification is done and you’re asking Dafny to compile your program, the compiler will complain, because it doesn’t know how to synthesize code for the method specification you wrote.

You can also do this with loops. For example, you can write
```dafny
while i < N
  invariant s == i * (i + 1) / 2
```
and not give a body. Again, the verifier is happy and will gladly check the rest of the code that follows the loop. This allows you to write down the loop invariant and make sure that the code after the loop is fine, only to later return to filling in the loop body.

If you leave off the body of a loop, Dafny will gently remind you of this by giving a warning like “this loop statement has no body”.

The forall statement is an aggregate statement. It simultaneously performs something for all values of the bound variables. In proofs, the forall statement is used as the counterpart of what logicians call “universal introduction”. In code, the forall statement has various restrictions, and is typically used to initialize all elements of an array.
The forall statement can also be declared without a body. Again, the verifier is happy to reason about its use, but the compiler would complain that there’s no body.

So, in the end, you do need to prove a body for your forall statements. You’ll have to make sure the body establishes the postcondition of the forall statement.

And even for functions and lemmas without bodies, even though the verify does not complain, they are unproved assumptions in your program.
