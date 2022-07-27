---
title: ERROR --- name of datatype (String) is used as a function
---

How do I fix this error message?:
```
{% include ERROR_OpenDatatype.dfy %}
```
which produces
```
{% include ERROR_OpenDatatype.txt %}
```


This is a case where you have to reveal the details of the datatype `String`.
So use `reveals String` instead of `provides String`:
```
{% include ERROR_OpenDatatype1.txt %}
```

