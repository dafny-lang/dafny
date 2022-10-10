---
title: "Error: insufficient reads clause to invoke function"
---

Example: This code
```
{% include_relative ERROR_InsufficientReads.dfy %}
```
produces this output:
```
{% include_relative ERROR_InsufficientReads.txt %}
```

This error message indicates that a nested call of a function needs a bigger `reads` set than its enclosing function provides.

Another situation provoking this error is this:
```dafny
class A {
  var x: int
  predicate IsSpecial() reads this {
    x == 2
  }
}
type Ap  = x : A | x.IsSpecial() witness *
```
In this case the error message is a bit misleading. The real problem is that the predicate in the subset declaration (that is, `x.IsSpecial()`)
is not allowed to depend on the heap, as `IsSpecial` does. If such a dependency were allowed, then changing some values in the heap could
possibly change the predicate such that a value which was allowed in the subset type now suddenly is not. This situation would be a disaster for both
soundness and ease of reasoning.

Another variation on the above is this example:
```dafny
trait A { var x: int }
type AZero = a: A | a.x == 0 witness *
```
where again the predicate depends on a heap variable `x`, which Dafny does not permit.

And a final example:
```dafny
datatype Foo = Foo | Foofoo

class Bar {
  var foo: set<Foo>;
  function method getFoo(): set<Foo> { this.foo }
}
```
which produces `Error: insufficient reads clause to read field`. In this case the function `getFoo` does indeed have an insufficient reads clause, as
it does not have one, yet it reads a field of `this`. You can insert either `reads this` or ``reads this`foo`` before the left brace.

The code in the original question is fixed like this:
```
{% include_relative ERROR_InsufficientReads1.dfy %}
```
