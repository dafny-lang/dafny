---
title: "Error: a modifies-clause expression must denote an object or a set/iset/multiset/seq of objects (instead got map<int, A>)"
---


Here is example code that produces the given error message:
```dafny
{% include_relative ERROR_ModifiesValue.dfy %}
```

The expression in the modifies clause is expected to be a set of object references.
It is permitted also to be a comma-separated list of object references or sets or sequences of such references.
In this example, the expression is none of these; instead it is a `map`.
`map`s are values and so are not modified; new values are created, just like an integer is not modified --- one computes a different integer value.

If the intent here is to say that any of the `A` objects stored in the map may be modified, then one has to construct a set of all those objects.
For a map, there is an easy way to do this: just say `m.Values`, as in this rewrite of the example:
```
{% include_relative ERROR_ModifiesValue1.dfy %}
```
