---
title: "Error: cannot establish the existence of LHS values that satisfy the such-that predicate"
---
## Question

What does this error mean?: "Error: cannot establish the existence of LHS values that satisfy the such-that predicate"
```
{% include_relative ERROR_NoLHS.dfy %}
```

## Answer

When a _such-that_ (`:|`) initialization is used, Dafny must be able to establish that there is at least one value
that satsifies the predicate given on the RHS. In this case if the map `m` is empty, there is not such value,
so the error message results.

If you add a precondition that the map is non-empty, then the error is gone:
```
{% include_relative ERROR_NoLHS1.dfy %}
```
