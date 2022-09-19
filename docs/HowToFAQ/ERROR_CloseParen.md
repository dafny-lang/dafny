---
title: "Error: closeparen expected"
---

## Question

What causes the error "Error: closeparen expected" as in

```dafny
{% include_relative ERROR_CloseParen.dfy %}
```
producing
```text
{% include_relative ERROR_CloseParen.txt %}
```

## Answer

You are writing a Java/C parameter declaration. In Dafny, parameter declarations have the form `name: type`, so
```dafny
method test(i: int) { ... }
```
