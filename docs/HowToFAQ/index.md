---
title: How-to and FAQ Guide for Dafny users
---

This page is the table of contents for a compendium of mini-lessons on Dafny programming idioms, how to accomplish various programming tasks in Dafny, how to fix error messages,
answers to FAQs or even just occasionally asked questions, and even information that you may not have asked yet, but you might.

These pages are not intended to be a reference manual or an organized tutorial for Dafny.

If you have questions that are not addressed here, be sure to communicate them to the Dafny team.

# FAQs
## Dafny language

- ["Is there a way to specify that all fields of an object, except a given one, don’t change?"](FAQModifiesOne)
- ["How do labels in preconditions work?"](FAQPreconditionLabels)
- ["What do attributes {:java "java", "lang"} mean? Where are attributes documented?"](FAQJavaAttribute)
- ["Is there a way to ask Dafny to die on its first verification failure?"](FAQDie)
- ["I can define a trait with some type parameters say trait `Test<A, B, C>`. When I use this trait is there a way to get Dafny to infer these types for me?"](FAQTypeInference)
- ["Does Dafny have monadic error handling?"](FAQMonadic)
- ["What is the `:-` operator?"](FAQElephant)
- ["How does `:-` work? I'm getting an unexpected failure."](FAQElephant)
- ["What is the meaning of and differences among `->`, `-->`, `~>`?"](FAQFunctionTypes)
- ["What is the difference between `function`, `method`, `function method`, and `function by method`?"](FAQFunctionMethodDiffs)
- ["Is it possible to restrict a type parameter to be a reference type? I see you can use T(!new) but I’m looking for the opposite."](FAQTypeParameterRestriction)
- ["A `seq` is an object reference, right?"](FAQReferences)

