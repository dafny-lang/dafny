---
title: "Error: rbrace expected"
---

## Question

Why am I getting an error saying "rbrace expected"?

## Answer

This is a common occurence caused by some parsing error within a brace-enclosed block, such as a module declaration, a class declaration, or a block statement.
The error means that the parser does not expect whatever characters it next sees. Consequently, the parser just says that it expects the block to be cloased by a right curly brace (`}`).

Here are some examples:

- A misspelled keyword introducing the next declaration
```
{% include_relative ERROR_Rbrace4.dfy %}
```
- A `const` initializer follows ':=', not '='
```
{% include_relative ERROR_Rbrace1.dfy %}
```
- A field (`var`) does not take an initializer
```
{% include_relative ERROR_Rbrace3.dfy %}
```
- A field (`var`) does not take an initializer, and if it did it would follow a `:=`, not a `=`
```
{% include_relative ERROR_Rbrace2.dfy %}
```
