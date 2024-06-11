---
title: "Error: cannot establish the existence of LHS values that satisfy the such-that predicate"
---

Here is example code that produces this error:
```dafny
{% include_relative ERROR_NoLHS.dfy %}
```


When a _such-that_ (`:|`) initialization is used, Dafny must be able to establish that there is at least one value
that satisfies the predicate given on the RHS. 
That is, in this case, it must prove
`assert exists k :: k in m;`.
But for this example, if the map `m` is empty, there is no such value,
so the error message results.

If you add a precondition that the map is non-empty, then the error is gone:
```
{% include_relative ERROR_NoLHS1.dfy %}
```
