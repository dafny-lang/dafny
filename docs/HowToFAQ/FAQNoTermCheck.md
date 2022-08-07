---
title: Can I ask dafny to not check termination of a function?
---

## Question

Can I ask dafny to not check termination of a function?

## Answer

FUnctions must always terminate, and it must be proved that they terminate.

Methods on the other hand should also terminate , but you can request tht the proof be skipped usig `decreases *` sa in
```dafny
method inf(i: int)
    decreases *
  {
      inf(i); 
  }
```

Eventually you should put an actual termination metric in place of the `*` and prove termination.
The reference manual has more information about termination metrics [in the section on `decreases` clauses](https://dafny.org/dafny/DafnyRef/DafnyRef#sec-decreases-clause).
