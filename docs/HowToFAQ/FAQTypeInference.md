---
title: I can define a trait with some type parameters say trait Test<A, B, C>. When I use this trait is there a way to get Dafny to infer these types for me?
---

## Question

I can define a trait with some type parameters say trait `Test<A, B, C>`. When I use this trait is there a way to get Dafny to infer these types for me?

## Answer

Type inference, though quite extensive in its effect, only works within the bodies of functions and methods.
Types in signatures and actual values for type parameters need to be written explicitly.
