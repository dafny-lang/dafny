---
title: "Why does Dafny not know this obvious property of maps?"
---

** Question: Why does Dafny not know this obvious property of maps?

I have this simple program:

```dafny
method mmm<K(==),V(==)>(m: map<K,V>, k: K, v: V) {
    var mm := m[k := v];
    assert v in mm.Values;
  }
```

The value `v` has just been inserted into the map. Why can't Dafny prove that `v` is now an element of the map?

** Answer

Dafny does not include all possible properties of types in its default set of axioms. The principal reason for this
is that including all axioms can give Dafny too much information, such that finding proofs becomes more time-consuming
for all (or most) problems. The trade-off is that the user has to give hints more often.

In this particular example, in order for Dafny to prove that `v` is in `mm.Values`, it needs to prove that
`exists k': K :: k' in mm.Keys && mm[k'] == v`. This is a difficult assertion to prove; the use of the axiom is not triggered
unless there is some term of the form `_ in mm.Keys` present in the assertions. So the proof is made much easier if we
first assert that `k in mm.Keys`; then Dafny sees immediately that `k` is the `k'` needed in the exists expression.
So
```dafny
method mmm<K(==),V(==)>(m: map<K,V>, k: K, v: V) {
    var mm := m[k := v];
    assert k in mm.Keys;
    assert v in mm.Values;
  }
```
proves just fine.
