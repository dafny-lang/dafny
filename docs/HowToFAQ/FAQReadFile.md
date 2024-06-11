---
title: How do I read a file as a string?
---

## Question

How do I read a file as a string? 

## Answer

You can't in pure Dafny. Not yet. Such a capability will eventually be part of a standard IO library.

What you can do is to write such a function in another language, say Java, and then use it in Dafny by extern declarations.
