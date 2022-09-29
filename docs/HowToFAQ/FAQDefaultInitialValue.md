---
title: How does one declare a type to have a "default" initial value, say a type tagged with {:extern}?
---

## Question

How does one declare a type to have a "default" initial value, say a type tagged with {:extern}?

## Answer

There is no general way to do this. Subset types and newtypes have [witness](../DafnyRef/DafnyRef/#sec-witness-clauses) clauses and types that are [auto-initializable](../DafnyRef/DafnyRef#sec-auto-init)
have a default, but those rules do not apply to anonymous extern types.
Particularly for opaque types, there is not even a way to infer such a value.

You can manually initialize like this:
```dafny
type {:extern} TT {
}
function method {:extern} init(): TT

method mmm() {
  var x: TT := init();
  var y:= x;
}
```

