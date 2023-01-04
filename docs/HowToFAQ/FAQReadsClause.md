---
title: Where do I put the reads clause in a subset type?
---

## Question:

This example
```dafny
{% include_relative FAQReadsClause.dfy %}
```
generates this error:
```text
{% include_relative FAQReadsClause.txt %}
```
but there is no obvious place to put a `reads` clause.

## Answer:

There is no place for the `reads` clause because no such clause should be needed.
A type definition is not allowed to depend on a mutable field;
the predicate in the subset type must be pure.

The general idiom is to add a predicate, often named `Valid()`, to a class that
reads its fields and returns `true` if the class members are appropriately consistent. 
Then call `Valid()` in the pre- and post-conditions of methods and in
preconditions of functions and predicates. Here is an example:

```dafny
class A {
  var x: string
  var y: string
  predicate Valid() reads this {
    |x| == |y|
  }
}

method Test(a: A)
  requires a.Valid()
  requires a.x == ""
  modifies a
  ensures a.Valid()
{
  assert a.Valid(); // That's correct thanks to the precondition.
  a.x := "abc"; // Because |a.y| == 0, we broke the Valid() predicate
  assert !a.Valid(); // But that's ok.
  a.y := "bca";
  assert a.Valid(); // Now Dafny can prove this
  // The postcondition holds
}
```

The [`{:autocontracts}`]({../DafnyRef/DafnyRef#sec-attributes-autocontracts}) attribute can be helpful here.

Note that the idiom using `Valid()` above is similar to the use of class invariants in other 
specification languages.

