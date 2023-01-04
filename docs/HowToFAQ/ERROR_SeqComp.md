---
title: "Error: could not prove function precondition"
---

This error can occur when trying to write a sequence comprehension expression like
```dafny
{% include_relative ERROR_SeqComp.dfy %}
```
which produces
```text
{% include_relative ERROR_SeqComp.txt %}
```

The problem is that current Dafny does not implicitly impose the condition that the function used to initialize the 
sequence elements is only called with `nat` values less than the size of the new sequence. That condition has to be made explicit:
```dafny
{% include_relative ERROR_SeqComp1.dfy %}
```
