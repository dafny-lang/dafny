---
title: Is there a way to test that two types are the same?
---

## Question

Is there a way to test that two types are the same, as in this exmple:
```
{% include_relative FAQTypeCompare.dfy %}
```

## Answer

No. Types are not first-class entities in Dafny. There are no variables or literals of a type `TYPE`.
There is a type test for reference types, namely `is`, but that is not a strict type equality but a
test that the dynamic type of a reference object is the same as or derived from some named type.
