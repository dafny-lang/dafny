---
title: How do I disambiguate module names?
---

## Question

How do I disambiguate module names in an example like this:
```dafny
{% include_relative FAQModuleNames0.dfy %}
```

## Answer

There is no direct syntax to do what is wanted here.
If you have control of the names, perhaps some renaming or moving the top-level `util` to be a sub-module of another module.
If this structure cannot be changed, then the following somewhat ugly code is a work-around:
```dafny
{% include_relative FAQModuleNames.dfy %}
```

There is discussion of defining syntax that names the top-level module, which would make an easy way to solve the above problem. See [this issue](https://github.com/dafny-lang/dafny/issues/2493).
