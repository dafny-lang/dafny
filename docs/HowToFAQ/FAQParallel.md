---
title: Does Dafny verify methods in parallel?
---

## Question

Does Dafny verify methods in parallel?

## Answer

For the most part, Dafny verifies each method in each module sequentially
and attempts to prove all the assertions in a method in one go.
However, you can use the option `/vcsCores:1` to parallelize some of the activity
and various options related to _verification condition splitting_ can break up the work
within a method. You can also start different instances of Dafny on different modules
in different host system processes to obtain some parallelization.


