---
title: A function seems to work just once. How do I get it to apply a bunch of times?
---

## Question

A function seems to work just once. How do I get it to apply a bunch of times?
Here is an example:
```
{% include_relative FAQFunctionUnroll0.dfy %}
```

The latter two lemmas will not prove without uncommenting the application of the lemma for one less iteration.
How can I get this to prove automatically?

## Answer

Function bodies are transparent. That is, when there is a call to a function in Dafny code, the body of the function
is available for reasoning about the effect of the function. But for recursive functions, it generally only does this once or twice, as that is 
usually sufficient to form an inductive proof. And always unrolling multiple times can reduce performance.

You can request that Dafny unroll a function multiple times by using the `{:fuel}` attribute.
The value of the attribute is the number of times the function will be unrolled. This is still a fixed upper limit,
but it does the trick in this case:
```
{% include_relative FAQFunctionUnroll1.dfy %}
```

A function will also keep unrolling if it has an argument that is a literal and that argument decreases
on each recursive call. So for this example we can write a helper function that takes a `nat` argument
and give it a literal value that tells it how much to unroll.
```
{% include_relative FAQFunctionUnroll2.dfy %}
```
With this solution, the number of unrollings can be set at the call site, rather than in the function definition.

[This paper](https://www.microsoft.com/en-us/research/publication/computing-smt-solver/) gives some technical insight into how recursive functions are handled in situations like these examples.

