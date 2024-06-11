---
title: How do I format a string?
---

## Question

How do I format a string?

## Answer

As of version 3.7.3, Dafny has no built-in or library capability to convert values to strings or to format them.
There is only the `print` statement that emits string representations of values to standard-out.

For now you will need to implement your own methods that convert values to strings, concatenating them to produce formatted strings.
