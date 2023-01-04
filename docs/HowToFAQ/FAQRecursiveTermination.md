---
title: Is there a simple way to prove the termination of a recursive function?
---

## Question

Is there a simple way to prove the termination of a recursive function?

Here is an example function:
```dafny
datatype Dummy = State1 | State2

function WalkState(str: string, s: Dummy): string {
  if str == [] then []
  else if s.State1? then WalkState(str[1..], Dummy.State2)
  else WalkState(str, Dummy.State1)
}
```

## Answer

In general, to prove termination of any recursive structure, one needs to declare a 
([well-founded](../DafnyRef/DafnyRef#sec-well-founded-orders)) measure that decreases on each iteration or recursive invocation;
because a well-founded measure has no infinitely decreasing sequences, the recursion must eventually terminate.
In many cases, Dafny will deduce a satisfactory (provable) measure to apply by default.
But where it cannot, the user must supply such a measure. A user-supplied measure is 
declared in a `decreases` clause. Such a measure is a sequence of expressions, ordered lexicographically by the
termination metric for each data type; the details of the ordering are 
explained in the [reference manual section on Decreases Clause](../DafnyRef/DafnyRef#sec-decreases-clause).

In the case of this example, the measure must be a combination of the length of the string, 
which decreases (and is bounded by 0) in the _else if_ branch and the state, 
creating a measure in which `Dummy.State1` is less than `Dummy.State2` and so decreases in the
final _else_ branch. So we can write
```dafny
datatype Dummy = State1 | State2

function WalkState(str: string, s: Dummy): string 
  decreases |str|, if s.State2? then 1 else 0
{
  if str == [] then []
  else if s.State1? then WalkState(str[1..], Dummy.State2)
  else WalkState(str, Dummy.State1)
}
```
which then proves without further user guidance.

