---
title: Cannot export mutable field 'x' without revealing its enclosing class 'A'
---

An example of this error is the code
```dafny
{% include_relative ERROR_MutableField.dfy %}
```
which produces the error
```text
{% include_relative ERROR_MutableField.txt %}
```

By only providing `A`, importers will know that `A` is a type, 
but won’t know that it is a reference type (here, a class). 
This makes it illegal to refer to a mutable field such as in the reads clause. 
So, you have to export A by revealing it.

Note, `export reveals A` does not export the members of A 
(except, it does export the anonymous constructor of A, if there is one). 
So, you still have control over which members of A to export.

The following code verifies without error:
```dafny
{% include_relative ERROR_MutableField1.dfy %}
```


