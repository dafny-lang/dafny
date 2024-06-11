---
title: What's the syntax for paths in include directives? How do they get resolved?
---

## Question

What's the syntax for paths in include directives? How do they get resolved?

## Answer

An include directive  is the `include` keyword followed by a string literal (in quotes).
The string is a conventional file path for the OS on which you are running and is the full file name with extension.
The filepath can be either absolute or relative; if relative, it is relative to the current working directory 
(i.e., the result of `pwd` on Linux).

As of version 3.7.3, there is no "include path" that might allow paths relative to other locations, but it is a feature request.
