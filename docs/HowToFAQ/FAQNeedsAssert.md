---
title: Why does Dafny need an obvious assert?
---

## Question:

Why does Dafny need the assert in this example:
```
lemma Foo<T>(s: seq<T>, p: seq<T> -> bool)
  requires p(s[..|s|])
  ensures p(s)
{
  assert s[..|s|] == s;
}
```

## Answer

Not all facts about built-in types are built-in to Dafny.
Some, like this one, need to be asserted or otherwise provided as provable lemmas.

The reason is that trying to provide all seemingly obvious facts is both
a never-ending chase and, importantly, can lead to trigger loops, proof instabilities, and overall poor performance.
The importance of having proofs be stable and performance be generally fast outweighs building in all the properties of built-in types that might otherwise be reasonable.

