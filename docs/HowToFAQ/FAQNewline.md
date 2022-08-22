---
title: It looks like, when compiling to C#, my print statements don't show up if I don't have \n at the end of the string.
---

## Question

It looks like, when compiling to C#, my print statements don't show up if I don't have \n at the end of the string.

## Answer

This is likely to be platform-dependent problem; the problem is whether the I/O system for the target platform does a flush of the output streams prior to terminating a program. The workaround is for the user program to do a `print "\n";` at the end of the program.

Dafny Issue #2559 notes this problem.
