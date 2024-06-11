---
title: How do `{:split_here}` and `{:focus}` work to divide up a proof?
---

## Question

How do `{:split_here}` and `{:focus}` work to divide up a proof?

## Answer

Verifying a method requires proving a large number of assertions.
Dafny uses a backend prover (an SMT solver) to verify assertions. The prover may become better or worse at verifying an assertion if you ask it to also verify another assertion. 
Dafny allows you to split up a group of assertions into batches, where each batch is sent to the SMT solver separately, so the verification of each batch is not influenced by the others.


One default way of operating is to combine all assertions into one batch, leading to a single run of the prover. 
 However, even when this is more efficient than the combination of proving each
assertion by itself (with prover start-up costs and the like for each one), it can also take quite a while to give a final result, possibly even timing-out.

So sometimes it is preferable to prove each assertion by itself, using the `-vcsSplitOnEveryAssert` command-line option.

But there are also intermediate options. Look at the various command-line options under "Verification-condition splitting".

Another way to split up the way in which assertions are grouped for proof is to use the two attributes `{:focus}` and `{:split_here}`,
both of which are applied to assert statements.

In brief, `{:focus}` says to focus on the block in which the attribute appears. Everything in that block is one assertion batch and everything
outside that block is another assertion batch. It does not matter where in the block the `{:focus}` attribute appears. If there are multiple
`{:focus}` attributes, each block containing one (or more) is one assertion batch, and everything outside of blocks containing `{:focus}` attributes
is a final assertion batch. This attibute is usually used to break out if-alternatives or loop-bodies into separate verification attempts.

`{:split_here}` creates an assertion batch of all assertions strictly before the attributed statement and another of the assertions at or after
the attributed statement. This attribute is usually used to break up long stretches of straight-line code.

Some examples that show how this works for multiple nested blocks are given in the reference manual, [here](../../DafnyRef/DafnyRef#sec-focus) and [here](../../DafnyRef/DafnyRef#sec-split_here).
