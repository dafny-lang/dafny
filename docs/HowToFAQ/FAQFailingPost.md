---
title: I can assert a condition right before a return, so why does the postcondition fail?
---

## Question

I can assert a condition right before a return, so why does the postcondition fail?

## Answer

There can be lots of reasons why a postcondition might fail to verify, but if you can prove the same predicate just before a return, 
a typical reason is that there are other exit paths from the method or function. There might be other `return` statements, but a
harder to spot exit path is the `:-` let-or-fail assignment.
Here is a sketch of that kind of problem:

```dafny
method test(MyClass o) returns (r: Result<int>)
  modifies o;
  ensures o.ok == true;
{
  o.ok := true;
  o.data :- MyMethod(o);
  assert o.ok;
  return;
}
```
This method can exit either through the `return` at the end or through the failure return if a failure value is returned
from `MyMethod`. That return happens before the `assert` that is intended to do a pre-check of the postcondition; depending
on the action of `MyMethod`, the target predicate may not be always true.
  
