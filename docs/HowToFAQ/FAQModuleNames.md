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
