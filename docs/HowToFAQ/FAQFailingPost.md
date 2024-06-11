---
title: I can assert a condition right before a return, so why does the postcondition fail to verify?
---

## Question

I can assert a condition right before a return, so why does the postcondition fail to verify?

## Answer

There can be lots of reasons why a postcondition might fail to verify, but if you can prove the same predicate just before a return, 
a typical reason is that there are other exit paths from the method or function. There might be other `return` statements, but a
harder to spot exit path is the `:-` let-or-fail assignment.
Here is a sketch of that kind of problem:

```dafny
include "library/Wrappers.dfy"

method test(MyClass o) returns (r: Wrappers.Result<int>)
  modifies o;
  ensures o.ok == true;
{
  o.ok := true;
  o.data :- MyMethod(o);
  assert o.ok;
  return;
}
```
(This example uses the `Result` type from the [standard library](https://github.com/dafny-lang/libraries/blob/master/src/Wrappers.dfy). The `include` directive in the example requires that you have a copy of the standard library in `./library`.)

This method can exit either through the `return` at the end or through the failure return if a failure value is returned
from `MyMethod`. That return happens before the `assert` that is intended to do a pre-check of the postcondition; depending
on the action of `MyMethod`, the target predicate may not be always true.
  
