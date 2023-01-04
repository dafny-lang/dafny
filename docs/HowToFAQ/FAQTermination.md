---
title: Is there a way to disable termination checks for recursive predicate definitions that I know to be logically consistent?
---

## Question

Is there a way to disable termination checks for recursive predicate definitions that I know to be logically consistent?

## Answer

Well, first of all, be careful about thinking things like "I know this to be logically consistent". Verifiers exist to check our human tendency to hand-wave over questionable assumptions.

That said, you can do something like this:

```dafny
predicate P(x: int, terminationFiction: int)
  decreases terminationFiction
{
  assume 0 < terminationFiction;
  P(x, terminationFiction - 1)
}
```

That may cause some quantification triggering problems and may need an axiom like
```
forall x,j,k:int :: P(x, j) == P(x, k)
```

It can also help to manually instantiate an axiom to avoid triggering issues:
declare the axiom like this:
```dafny
lemma {:axiom} PSynonym(x: int, j: int, k: int)
  ensures P(x, j) == P(x, k)
```
and then call the lemma as needed.
