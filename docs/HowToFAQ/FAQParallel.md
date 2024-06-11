---
title: Does Dafny verify methods in parallel?
---

## Question

Does Dafny verify methods in parallel?

## Answer

When used on the command-line, Dafny verifies each method in each module sequentially
and attempts to prove all the assertions in a method in one go.
However, you can use the option `/vcsCores` to parallelize some of the activity
and various options related to _verification condition splitting_ can break up the work
within a method.

When used in the IDE, the default is concurrent execution of proof attempts.

