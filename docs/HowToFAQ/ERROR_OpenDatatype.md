---
title: ERROR --- name of datatype (String) is used as a function
---

How do I fix this error message?:
```
{% include_relative ERROR_OpenDatatype.dfy %}
```
which produces
```
{% include_relative ERROR_OpenDatatype.txt %}
```


This is a case where you have to reveal the details of the datatype `String`.
So use `reveals String` instead of `provides String`:
```
{% include_relative ERROR_OpenDatatype1.txt %}
```

