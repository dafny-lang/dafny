---
title: "How do I write specifications for a lambda expression in a sequence constructor?"
---

## Question

How do I write specifications for a lambda expression in a sequence constructor?

## Answer

Consider the code
```dafny
class C {
  var p: (int, int);
}

function method Firsts0(cs: seq<C>): seq<int> {
  seq(|cs|, i => cs[i].p.0) // Two errors: `[i]` and `.p`
}
```

Dafny complains about the array index and an insufficient reads clause in the lambda function.
Both of these need specifications, but where are they to be written.

The specifications in a lamda function expression are written after the formal aarguments
but before the `=>`.

The array index problem is solved by an appropriate `requires` clause:
```dafny
class C {
  var p: (int, int);
}

function method Firsts0(cs: seq<C>): seq<int> {
  seq(|cs|, i requires 0 <= i < |cs| => cs[i].p.0) // Two errors: `[i]` and `.p`
}
```

and the reads problem by an appropriate `reads` clause:

```dafny
class C {
  var p: (int, int);
}

function method Firsts2(cs: seq<C>): seq<int>
  reads set i | 0 <= i < |cs| :: cs[i]
{
  seq(|cs|, i
    requires 0 <= i < |cs|
    reads set i | 0 <= i < |cs| :: cs[i] => cs[i].p.0)
}
```
