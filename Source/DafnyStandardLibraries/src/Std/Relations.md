## The `Relations` module

The `Relations` module defines a number of properties on relations, 
where the relation is defined by a predicate that takes two values of the same type.

Example properties:
- Reflexive: `R(x,x)` is true
- Irreflexive: `R(x,x)` is false
- AntiSymmetric: `R(x,y) && R(y,x) ==> x==y`
- Transitive : `R(x,y) && R(y,z) ==> R(x,z)`
- Connected : `x != y ==> R(x,y) || R(y,x)`
- StronglyConnected : `R(x,y) || R(y,x)`
- TotalOrdering : Reflexive, AntiSymmetric, Transitive, StronglyConnected (e.g., `<=` on integers)
- StrictTotalOrdering : Irreflexive, AntiSymmetric, Transitive, Connected (e.g., `<` on integers)

These properties are sometimes required for other functions. For example,
if one wants to sort a sequence by some relation `R`, one must establish that `R` is a _Total Ordering_
or a _Strict Total Ordering_.
In fact, that is part of the precondition of a sorting function.

As a simple example, you might define a predicate like this:
<!-- %check-resolve %save tmp-intlt.dfy -->
```dafny
  const IntLT := ((i: int, j: int) => (i < j))
```

and then need to prove this lemma to use it in a sorting routine:
<!-- %check-verify %use tmp-intlt.dfy -->
```dafny
  import opened Std.Relations
  lemma IntLTisStrictTotalOrder()
    ensures StrictTotalOrdering(IntLT) {}
```

Fortunately, Dafny proves this without aid.

All these definitions are ghost predicates; they are used as part of proofs rather than in compiled code.