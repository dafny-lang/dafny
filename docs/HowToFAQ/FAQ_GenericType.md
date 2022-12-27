---
title: Is there a way I can pass a variable with a generic type to a method with a concrete type?
---

## Question

Is there a way I can pass a variable with a generic type to a method with a concrete type? Here is some motivating code:
```dafny
predicate Goo<K, V>(m: map<K, V>)
  requires m.keyType is string // Can I do something like this?
{ Foo(m) }

predicate Foo<V>(m: map<string, V>)
```

## Answer

In short, no.

There are a few problems here. First there is no way to extract the type of the keys of a map as a _type_ value. Dafny does not have the capability to reason about 
types as first-class entities. In fact the `is` operator takes a value and a type, not two types.

We could try writing the precondition as `requires m.Keys is set<string>`, but that is not permitted either as `m.Keys` is a `set<K>` and is not comparable to `set<string>` with `is`.
 
