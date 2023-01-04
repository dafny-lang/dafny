---
title: Dafny doesn’t like when a type and a module have the same name. How can I fix this?
---

## Question

Dafny doesn’t like when a type and a module have the same name. How can I fix this?
```
{% include_relative FAQNameConflict.dfy %}
```
produces
```
{% include_relative FAQNameConflict.txt %}
```

## Answer

The problem is that in the `Test` module, the name `Result` is both a module name and a datatype name.
The module name takes precedence and so the resolution error happens.
(Despite the error message, modules never have type arguments.)

This situation can be fixed two ways. First, write `Result.Result` to mean the datatype. Or second, 
import the module with a new name, such as `import opened R = Result`. Then inside module Test, there is
the name `R` for a module and the name `Result` for the datatype. The following code shows both these options.
```
{% include_relative FAQNameConflict1.dfy %}
```
