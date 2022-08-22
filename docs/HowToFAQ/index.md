---
title: How-to and FAQ Guide for Dafny users
---

This page is the table of contents for a compendium of mini-lessons on Dafny programming idioms, how to accomplish various programming tasks in Dafny, how to fix error messages,
answers to FAQs or even just occasionally asked questions, and even information that you may not have asked yet, but you might.

These pages are not intended to be a reference manual or an organized tutorial for Dafny.

If you have questions that are not addressed here, be sure to communicate them to the Dafny team.

# FAQs
## Dafny language

- ["How do I make a singleton instance of a class for repeated later use?](FAQSingleton)
- ["Is there a way to write `if foo().equals(bar()) { x } else { y }` where `foo` and `bar` are methods?](FAQMethodSequence)
- ["If I have an assertion about a class and a loop that doesn't mention (read, modify)  the class, why does dafny fail to establish the assertion after the loop?"](FAQLoopModifies)
- ["I can assert a condition right before a return, so why does the postcondition fail?](FAQFailingPost)
- ["How can I combine sequences of different types?"](FAQSeqTrait)
- ["How do I disambiguate module names?](FAQModuleNames)
- ["A function seems to work just once. How do I get it to apply a bunch of times?"](FAQFunctionUnroll)
- ["Why is my import opened statement not working?"](FAQModuleImport)
- ["Is there a way to test that two types are the same?"](FAQTypeCompare)
- ["When a lemma has multiple ensures clauses, I’m finding that they interact, when I expected them to be independent.  For example, commenting out one of them can make another one not verify.  How should I think about this?"](FAQMultClauses)

