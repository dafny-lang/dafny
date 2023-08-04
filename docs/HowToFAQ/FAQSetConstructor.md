---
title: "Why does Dafny complain about this use of a set constructor: `set i: int | Contains(i)`?"
---

## Question

Why does Dafny complain about this use of a set constructor: `set i: int | Contains(i)`?
Here is an example:
```dafny
module test {

  ghost const things: set<int>

  predicate Contains(t: int) 
  {
    t in things
  }

  function ThisIsOk(): set<int> {
    set i: int | i in things && i > 0
  }

  function ThisIsNotOk(): set<int> {
    set i: int | Contains(i) && i > 0
  }

}
```

which produces the error "the result of a set comprehension must be finite, but Dafny's heuristics can't figure out how to produce a bounded set of values for 'i'".

## Answer

In constructing a `set`, which must be finite, Dafny must prove that the set is indeed finite.
When the constructor has `i in things` inlined, Dafny can see that the set of values of `i` for which the predicate is true can be no larger than `things`, which is already known by declaration to be 
a finite set. However, when the predicate is `Contains`, Dafny cannot in general see that fact.
The Dafny's heuristic for determining that the constructor is producing a finite set does not
inspect the body of `Contains` even though that is a transparent function. Note that if the constructor and the return type of `ThisIsNotOK` is made `iset`, Dafny does not complain.

An alternate general way to refine a set is given by this example:
```dafny
module test {

  ghost const things: set<int>

  function RefineThings(condition: int -> bool): set<int>
  {
    set t: int | t in things && condition(t)
  }

  function ThisIsOk(): set<int> {
    set i: int | i in things && i > 0
  }

  function ThisIsOkAgain(): set<int> {
    RefineThings(i => i > 0)
  }
}
```
