---
title: Error - insufficient reads clause to invoke function
---

Example: This code
```
{% include_relative ERROR_InsufficientReads.dfy %}
```
produces this output:
```
{% include_relative ERROR_InsufficientReads.txt %}
```

This error message indicates that a nested call of a function needs a bigger `reads` set than its enclosing function provides.
