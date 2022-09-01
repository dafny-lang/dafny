---
title: Is there a nice way to turn a `set` into a `seq`?
---

## Question

Is there a nice way to turn a set into a seq?

## Answer

There is as yet no built-in simple function but there are various idioms that can accomplish this task.

Within a method (where you can use a while loop), try `var acc: seq<int> := []; 
  while s != {} { var x: int :| x in s; acc := acc + [x]; s := s - {x}; }`

You could use a function-by-method to encapsulate the above in a function.

Here is an extended example taken from  [Dafny Power User: Iterating over a Collection](http://leino.science/papers/krml275.html).

```dafny
function method SetToSequence<A(!new)>(s: set<A>, R: (A, A) -> bool): seq<A>
  requires IsTotalOrder(R)
  ensures var q := SetToSequence(s, R);
    forall i :: 0 <= i < |q| ==> q[i] in s
{
  if s == {} then [] else
    ThereIsAMinimum(s, R);
    var x :| x in s && forall y :: y in s ==> R(x, y);
    [x] + SetToSequence(s - {x}, R)
}

lemma ThereIsAMinimum<A(!new)>(s: set<A>, R: (A, A) -> bool)
  requires s != {} && IsTotalOrder(R)
  ensures exists x :: x in s && forall y :: y in s ==> R(x, y)
```
