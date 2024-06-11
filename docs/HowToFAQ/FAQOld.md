---
title: In an invariant, I want to say that once a boolean variable that starts false is set to true, it remains true forever.  Can I use old for this?
---

## Question

In an invariant, I want to say that once a boolean variable that starts false is set to true, it remains true forever.  Can I use old for this?

## Answer

Almost but not quite. `old` gives you the value of an expression in the method's pre-state or at given label. 
Equivalently. you can stash the value of an expression at some point in the control flow in some temporary (even ghost) variable.
Then you can state a predicate saying "if the expression was true at that specific point, then it is still true now when I am testing it".

But that is not quite saying "once an expression becomes true, it stays true".
For that you need a more complicated solution:
- declare a ghost variable `nowTrue`, initialized to `false`
- at every location where the expression (call it `e`) is set, 
   - first test its new value: `if nowTrue && !e { FAILURE }`
   - and then set the ghost value `nowTrue := nowTrue || e;`
