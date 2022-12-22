<p></p> <!-- avoids duplicate title -->

# Sets

Sets of various types form one of the core tools of verification for Dafny.
Sets represent an orderless collection of elements, without repetition. Like
sequences, sets are immutable value types. This allows them to be used easily
in annotations, without involving the heap, as a set cannot be modified once
it has been created. A set has the type:

<!-- %no-check -->
```dafny
  set<int>
```

for a set of integers, for example. In general, sets can be of almost any type, including objects. Concrete sets can be specified by using display notation:

<!-- %check-verify -->
```dafny
method m()
{
  var s1 := {}; // the empty set
  var s2 := {1, 2, 3}; // set contains exactly 1, 2, and 3
  assert s2 == {1,1,2,3,3,3,3}; // same as before
  assert s1 != s2;  // sets with different elements are different
  var s3, s4 := {1,2}, {1,4};
}
```

The set formed by the display is the expected set, containing just
the elements specified. For the case of the empty set, the type of the
variable `s1 above is not fully known from its initialization. However,
later `s1` is compared to `s2`, so it must have the same type as `s2`,
namely `set<int>`. However, in the example below, there is no such use of `s1`, 
so the type of `s1` must be specifically stated in its declaration.

Above we also see that equality is defined
for sets. Two sets are equal if they have exactly the same elements.
New sets can be created from existing ones using the common set operations:

<!-- %check-verify -->
```dafny
method m()
{
  var s1: set<int> := {};
  var s2 := {1, 2, 3};
  var s3, s4 := {1,2}, {1,4};
  assert s2 + s4 == {1,2,3,4}; // set union
  assert s2 * s3 == {1,2} && s2 * s4 == {1}; // set intersection
  assert s2 - s3 == {3}; // set difference
}
```

the union does not count repeated elements more than once. These
operators will result in a finite set if both operands are finite,
so they cannot generate an infinite set. Unlike the arithmetic
operators, the set operators are always defined. In addition to set
forming operators, there are comparison operators with their usual
meanings:

<!-- %check-verify -->
```dafny
method m()
{
  assert {1} <= {1, 2} && {1, 2} <= {1, 2}; // subset
  assert {} < {1, 2} && !({1} < {1}); // strict, or proper, subset
  assert !({1, 2} <= {1, 4}) && !({1, 4} <= {1}); // not subsets
  assert {1, 2} == {1, 2} && {1, 3} != {1, 2}; // equality and non-equality
}
```

Sets, like sequences, support the `in` and `!in` operators, to
test element membership. For example:

<!-- %check-verify-warn Sets.W1.expect -->
```dafny
method m()
{
  assert 5 in {1,3,4,5};
  assert 1 in {1,3,4,5};
  assert 2 !in {1,3,4,5};
  assert forall x: int :: x !in {};
}
```

Sets are used in several annotations, including reads and modifies
clauses. In this case, they can be sets of a specific object type
(like `Nodes` in a linked list), or they can be sets of the
generic reference type `object`. Despite its name, this can point to
any object or array. This is useful to bundle up all of the locations
that a function or method might read or write when they can be different types.


When used in a decreases clause, sets are ordered by proper subset.
To use sets in
decreases clauses, the successive values must be "related" in some sense, which
usually implies that they are recursively calculated, or similar.

You can test if a set is empty by comparing it to the empty set
(`s == {}` is true if and only if `s` has no elements.)



A useful way to create sets is using a set comprehension. This defines
a new set by including `f(x)`
in the set for all `x` of type `T` that satisfy `p(x)`:

<!-- %no-check -->
```dafny
  set x: T | p(x) :: f(x)
```

This defines a set in a manner reminiscent of a universal quantifier (`forall`). As with quantifiers,
the type can usually be inferred. In contrast to quantifiers, the bar syntax (`|`) is required to
separate the predicate (`p`) from the bound variable (`x`). The type of the elements of the resulting set is
the type of the return value of `f(x)`. The values in the constructed set are the return values of `f(x)`:
`x` itself acts only as a bridge between the predicate `p` and the function `f`. It
usually has the same type as the resulting set, but it does not need to. As an example:

<!-- %check-verify-warn Sets.W2.expect -->
```dafny
method m()
{
  assert (set x | x in {0,1,2} :: x + 0) == {0,1,2};
}
```

If the function is the identity, then the expression can be written with a particularly nice form:

<!-- %check-verify-warn Sets.W3.expect -->
```dafny
method m()
{
  assert (set x | x in {0,1,2,3,4,5} && x < 3) == {0,1,2};
}
```

To reason about general, non-identity functions in set comprehensions, Dafny may need some help.
For example, the following is true, but Dafny cannot prove it:

<!-- %check-verify Sets.1.expect -->
```dafny
method m()
{
  // assert {0*1, 1*1, 2*1} == {0,1,2};  // include this assertion as a lemma to prove the next line
  assert (set x | x in {0,1,2} :: x * 1) == {0,1,2};
}
```

To help Dafny prove this assertion, you can precede it with the assertion
`assert {0*1, 1*1, 2*1} == {0,1,2};`. This lets Dafny figure out both assertions.

<!-- %check-verify -->
```dafny
method m()
{
  assert {0*1, 1*1, 2*1} == {0,1,2};  // include this assertion as a lemma to prove the next line
  assert (set x | x in {0,1,2} :: x * 1) == {0,1,2};
}
```
Without care, a set comprehension could prescribe an infinite number of elements, but a `set`
is only allowed to have a finite number of elements. For example, if you tried writing
`set x | x % 2 == 0` as the set of all even integers, then you would get an error.
(If you really want an infinite set, use the `iset` type instead.
For example, `iset x | x % 2 == 0` is legal in ghost contexts.)
To ensure that `set` comprehensions give rise to finite sets, Dafny employs some heuristics.
When creating sets of integers, this can be done by bounding the integers
in at least one conjunct of the predicate (something like `0 <= x < n`). Requiring a bound
variable to be in an existing set also works, as in `x in {0,1,2}` from above.
