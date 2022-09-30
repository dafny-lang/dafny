---
title: Can I ask Dafny to not check termination of a function?
---

## Question

Can I ask dafny to not check termination of a function?

## Answer

Functions must always terminate, and it must be proved that they terminate.

Methods on the other hand should also terminate , but you can request the the proof be skipped using `decreases *`, as in
```dafny
method inf(i: int)
    decreases *
  {
      inf(i); 
  }
```

Eventually you should put an actual termination metric in place of the `*` and prove termination.
The reference manual has more information about termination metrics [in the section on `decreases` clauses](../DafnyRef/DafnyRef#sec-decreases-clause).
