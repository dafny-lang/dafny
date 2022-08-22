---
title: How-to and FAQ Guide for Dafny users
---

This page is the table of contents for a compendium of mini-lessons on Dafny programming idioms, how to accomplish various programming tasks in Dafny, how to fix error messages,
answers to FAQs or even just occasionally asked questions, and even information that you may not have asked yet, but you might.

These pages are not intended to be a reference manual or an organized tutorial for Dafny.

If you have questions that are not addressed here, be sure to communicate them to the Dafny team.

# FAQs
## Dafny language

- ["A module A has names from an `import opened` or another module B, but if C imports A, it does not get those names. Please explain."](FAQImportOpened)
- ["Are there functional alternatives to recursive calls that are more efficient or use less stack space?"](FAQRecursiveCalls)
- ["How do I read a file as a string?"](FAQReadFile)
- ["Can I ask dafny to not check termination of a function?"](FAQNoTermCheck)
- ["What does {:termination false} do on trait? It looks like it is required if I want to extend traits from other modules."](FAQTerminationFalse)
- ["How do I make Dafny termination checking happy with this pattern of mutual recursion?"](FAQMutualRecursion)
- ["Can it be proved that a class instance is not an instance of a trait?"](FAQTypeReasoning)
- ["Is there a nice way to turn a set into a seq?"](FAQSetToSeq)
- ["How do I declare a default value for a parameter of a method or function?"](FAQDefaultParameter)
- ["I just realized that a function I was compiling had a type-error inside a match case.  Instead of giving a compile error I was getting a redundant clause warning for the second case. What is the reason for this?"](FAQRedundantCase)
- ["Is there a way I can pass a variable with a generic type to a method with a concrete type?"](FAQ_GenericType)
- ["How can ghost code call methods with side effects?"](FAQGhostSideEffects)
- ["How do I create and use an iterator?](FAQIterator)
- ["Can classes appear in specs?"](FAQClassInSpec)

