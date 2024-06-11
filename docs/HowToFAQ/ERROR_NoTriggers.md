---
title: "Warning: /!\ No terms found to trigger on."
---

This warning occurred with the following code:
```dafny
predicate ExistsSingleInstance(s : string32, delim : string32)
  {
    exists pos : nat ::
      (pos <= |s| - |delim| && forall x : nat :: x < |delim| ==> s[pos + x] == delim[x]) &&
      forall pos' : nat :: (pos' <= |s| - |delim| && forall y : nat :: y < |delim| ==> s[pos' + y] == delim[y]) ==> pos == pos'
  }
```

The verifier uses quantifications by finding good ways to instantiate them.
More precisely, it uses `forall` quantifiers by instantiating them and it proves `exists` quantifiers by finding witnesses for them.
The warning you’re getting says that nothing stands out to the verifier as a good way to figure out good instantiations.

In the case of `pos`, this stems from the fact that a good instantiation would be some `pos` for which the verifier already knows either `pos <= …` or `forall x :: …`, the former of which is not specific enough and the latter is too complicated for it to consider.

The “no trigger” warning is fixed by this refactoring:
```dafny
predicate SingleInstance(s: string, delim: string, pos: nat)
{
  pos <= |s| - |delim| &&
  forall x : nat :: x < |delim| ==> s[pos + x] == delim[x]
}

predicate ExistsSingleInstance'(s: string, delim: string)
{
  exists pos : nat ::
    SingleInstance(s, delim, pos) &&
    forall pos' : nat :: SingleInstance(s, delim, pos') ==> pos == pos'
}
```

One more remark: The “no trigger” warning should be taken seriously, because it’s usually a sign that there will be problems with using the formula and/or problems with verification performance.
