---
title: Why do nested modules not see the imports of their enclosing modules?
---

## Question

Why is my import opened statement not working in the following example:
```
{% include_relative FAQModuleImport.dfy %}
```

## Answer

Although nested modules are nested inside other modules, they should really be thought of as their own module.
There is no particular benefit to module `A.B` from being nested inside module `A` --- none of the declarations of `A` are visible in `B` other than the names of sibling modules of `B`.
The benefit is to module `A`, for which the nested module `B` is a namespace that can group some related declarations together.

Accordingly, if you want some names from another module to be available within a submodule, you must import that directly in the submodule.
The example above becomes this:
```
{% include_relative FAQModuleImport1.dfy %}
```
