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

The array index problem is solved by a `requires` clause that limits the range of the index::
```dafny
class C {
  var p: (int, int);
}

function method Firsts0(cs: seq<C>): seq<int> {
  seq(|cs|, i requires 0 <= i < |cs| => cs[i].p.0) // Two errors: `[i]` and `.p`
}
```

and the reads complaint by a `reads` clause that states what objects will be read.
In this case, it is the objects `cs[i]` that have their `p` field read.
If the element type of `cs` were a value type instead of a reference type, this
`reads` clause would be unnneccessary.

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
