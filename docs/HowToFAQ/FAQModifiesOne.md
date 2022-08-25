---
title: Is there a way to specify that all fields of an object, except a given one, don’t change?
---

## Question

Is there a way to specify that all fields of an object, except a given one, don’t change?

## Answer

Instead of writing `modifies this` or `modifies o`, you can write ``modifies this`f`` of ``modifies `f``
to indicate that just the field `f` of `this` may be assigned to. Similarly you can use 
``modifies a`f`` for fields of other objects.
