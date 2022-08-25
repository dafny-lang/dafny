---
title: Is there a way to specify that all fields of an object, except a given one, don’t change?
---

## Question

Is there a way to specify that all fields of an object, except a given one, don’t change?

## Answer

Instead of writing `modifies this` or `modifies o`, you can write ``modifies this`f`` (equivalently ``modifies `f``)
or ``modifies o`f``
to indicate that just the field `f` of `this` or `o`, respectively, may be assigned to.
