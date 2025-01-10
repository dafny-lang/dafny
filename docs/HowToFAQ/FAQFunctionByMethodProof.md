---
title: I can't prove the equivalence between the method part of a `function by method`` and the function itself
---

## Question

I can't prove the equivalence between the method part of a function by method and the function itself.
It seems that my invariants can't be maintained by the loop, and I don't know how to prove them.

## Answer

Consider the simple problem of computing the sum of a sequence of integers.
You might be tempted to immediately write the following equivalence,
with your best guess of an invariant
and a hint at the end to help Dafny realize that the result is correct.
However you cannot prove the invariant you just wrote.

```
{% include_relative FAQFunctionByMethodProof1.dfy %}
```

Let's unroll the computation of the function on a sequence of 3 elements.
The function will compute:

`s[0] + (s[1] + (s[2] + 0))`

But the loop will compute

`((0 + s[0]) + s[1]) + s[2]`

In the function, we add the first element (`s[0]`) to the result of computing the sum of the remaining elements (`s[1] + (s[2] + 0))`).
In the by method, we add the last element (`s[2]`) to the accumulator, which contains the sum of the initial terms (`(0 + s[0]) + s[1]`).
If it was not the case that the addition was associative and 0 was a neutral element, there would be no immediate way to prove that the two computations are equivalent.

There are essentially three solutions around that:

* Improve the invariant, knowing `+` is associative
* Change the order of computation of the function so that it matches the by method
* Change the order of computation of the by method so that it matches the function

There are more intrusive solutions, such as making the function tail-recursive by changing the function's signature to include an accumulator or a sequence of callbacks to perform a the end, but we will explore only the one that don't change the signature of `Sum()`.

## Improved invariant

You can change the invariant to be `invariant result + Sum(s[i..]) == Sum(s)`, as below:

```
{% include_relative FAQFunctionByMethodProof2.dfy %}
```

This works because, with `result'` being the result at the end of the loop and `+` being associative,
the lemma `IntermediateProperty()` shows the underlying reasoning that helps prove that the invariant
is indeed invariant. Dafny can prove it automatically, so the lemma is not needed in the loop body.
One nice thing is that we can get rid of the final hint.

What if you had an operation more complex that "+", that is not associative?
This is when you need to ensure the loop and the function are computing in the same order.
Let's explore how to do so by changing either the function, or the by-method body.

## Make the function compute what the by-method does
The by-method loop's first addition is 0 plus the first element (`s[0]`) of the sequence. For this to
be the first addition performed by the function, it has to be at the bottommost level of the call.
Indeed, each addition is performed after the recursive call finishes. This means that
the function needs to sum the `n-1` elements first and add the remaining last one.

Since it's exactly what the method computes, it satisfies our initial invariant.

```
{% include_relative FAQFunctionByMethodProof3.dfy %}
```

Not only does this approach require more proof hints, but it might also break the proofs that dependend on the shape of the function, while all we wanted in the first place was to give a more efficient implementation to the function.
Therefore, it's reasonable to expect we will prefer to change the implementation of the by-method body to reflect the function, not the opposite, as follows:

## Make the by-method body compute what the function computes

To compute iteratively what the function computes recursively, you have to find what is the first
addition that will be computed by the method. As mentioned previously, the first addition is the one performed at the bottommost level of recursion: the first addition is `s[|s|-1] + 0`,
so the loop has to actually be in reverse, like this:

```
{% include_relative FAQFunctionByMethodProof4.dfy %}
```

Note that this approach results in the smallest invariant that actually closely matches the function itself.
Also, instead of adding to the right of `result`, adding to the left ensures the same order is kept,
in case the operation was not commutative (so that it would work for sequence append operation).