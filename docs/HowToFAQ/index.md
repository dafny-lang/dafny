---
title: How-to and FAQ Guide for Dafny users
---

This page is the table of contents for a compendium of mini-lessons on Dafny programming idioms, how to accomplish various programming tasks in Dafny, how to fix error messages,
answers to FAQs or even just occasionally asked questions, and even information that you may not have asked yet, but you might.

These pages are not intended to be a reference manual or an organized tutorial for Dafny.

If you have questions that are not addressed here, be sure to communicate them to the Dafny team.

# FAQs
## Dafny language

- ["How do I pattern match against a head and tail of a sequence or against a set?"](FAQMatchOnSet)
- ["How do I create a new empty map (or set or sequence)?"](FAQMepSetSeq)
- ["I have a module that exports a bunch of things. In another module I only need to use 1 thing. Is there a way to import only the thing that I want?"](FAQImportOneThing)
- ["What is the difference between `modifies this`, `modifies this.x`, and ``modifies this`x``?](FAQModifiesThis)
- ["How does one define a record?"](FAQRecord)
- ["What does `forall v :: v in vals ==> false` evaluate to if vals is non-empty?"](FAQTriggers)
- ["Why does Dafny complain about this use of a set constructor: `set i: int | Contains(i)`?"](FAQSetConstructor)
- ["What's the syntax for paths in include directives? How do they get resolved?"](FAQIncludes)
- ["How do `{:split_here}` and `{:focus}` work to divide up a verification condition?"](FAQSplitHere)
- ["How does one declare a type to have a default initial value, say a type tagged with {:extern}?'](FAQDefaultInitialValue)

