---
title: What is the `:-` operator? How does it work?
---

## Question

What is the `:-` operator? How does it work?

## Answer

This operator is called the _elephant operator_ (because it has a trunk).
It is used to write code that exits on failure (much like exceptions in other programming languages or the ? operator in Rust).
The topic is discussed at length in
the section of the reference manual on [Update with Failure statements](../DafnyRef/DafnyRef#sec-update-failure).

In brief, Dafny permits methods to return values of _failure-compatible_ types. If the result of a method is being assigned to a variable with the `:-` operator and the result is a failure, then the method exits immediately, with the failure being propagated to the calling method.
