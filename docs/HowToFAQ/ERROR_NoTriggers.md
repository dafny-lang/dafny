---
title: "Warning: /!\ No terms found to trigger on."
---

This warning occurred with the following code:
```dafny
predicate ExistsSingleInstance(s : string32, delim : string32)
  {
    exists i : nat :: i <= |s| - |delim| && forall x : nat :: x < |delim| ==> s[i + x] == delim[x] &&
      (forall j : nat :: j <= |s| - |delim| && forall y : nat :: y < |delim| ==> s[i + y] == delim[y] ==> i == j)
  }
```

The verifier uses quantifications by finding good ways to instantiate them.
More precisely, it uses `forall` quantifiers by instantiating them and it proves `exists` quantifiers by finding witnesses for them.
The warning you’re getting says that nothing stands out to the verifier as a good way to figure out good instantiations.

In the case of `i`, this stems from the fact that a good instantiation would be some `i` for which the verifier already knows either `i <= …` or `forall x :: …`, the former of which is not specific enough and the latter is too complicated for it to consider.

I’ll suggest a way to fix it, but first… I suspect you have not parenthesized the expression as you intended. What you have written parses as
```dafny
exists i : nat ::
  i <= |s| - |delim| &&
  forall x : nat :: x < |delim| ==>
    s[i + x] == delim[x] &&
    (forall j : nat :: j <= |s| - |delim| && forall y : nat :: y < |delim| ==> s[i + y] == delim[y] ==> i == j)
```
(where I’m using indentation to show how the connectives bind). I’m guessing you may have wanted to say
```dafny
exists i : nat ::
  (i <= |s| - |delim| && forall x : nat :: x < |delim| ==> s[i + x] == delim[x]) &&
  forall j : nat :: (j <= |s| - |delim| && forall y : nat :: y < |delim| ==> s[i + y] == delim[y]) ==> i == j
```
That is, I’m guessing you wanted to say there exists a unique `i` such that
`exists i : nat :: i <= |s| - |delim| && forall x : nat :: x < |delim| ==> s[i + x] == delim[x]`.


If so, then here is a way to both fix the meaning of the formula and fix the “no trigger” warning:
```dafny
predicate SingleInstance(s: string, delim: string, i: nat)
{
  i <= |s| - |delim| &&
  forall x : nat :: x < |delim| ==> s[i + x] == delim[x]
}

predicate ExistsSingleInstance'(s: string, delim: string)
{
  exists i : nat ::
    SingleInstance(s, delim, i) &&
    forall j : nat :: SingleInstance(s, delim, j) ==> i == j
}
```

One more remark: The “no trigger” warning should be taken seriously, because it’s usually a sign that there will be problems with using the formula and/or problems with verification performance.
