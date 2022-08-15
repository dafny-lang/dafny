---
title: "What do attributes {:java "java", "lang"} mean? Where are attributes documented?"
---

## Question

What do attributes {:java "java", "lang"} mean? Where are attributes documented?
```dafny
{% include_relative FAQJavaAttribute.dfy %}
```

## Answer

In general, attributes are documented in a chapter of the [reference manual](https://dafny.org/dafny/DafnyRef/DafnyRef#(sec-attributes); some are also documented in the sections in which the language feature for which they are relevant is described.
However, at present not all of them are documented.

As for `{:java}`, it is not a defined attribute (as of version 3.7.4). However, there are other projects that build on Dafny that may define and implement additional attributes of their own.

Keep in mind, that any attributes not recognized by Dafny are silently ignored, to allow for such extension.
