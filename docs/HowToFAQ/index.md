---
title: How-to and FAQ Guide for Dafny users
---

This page is the table of contents for a compendium of mini-lessons on Dafny programming idioms, how to accomplish various programming tasks in Dafny, how to fix error messages,
answers to FAQs or even just occasionally asked questions, and even information that you may not have asked yet, but you might.

These pages are not intended to be a reference manual or an organized tutorial for Dafny.

If you have questions that are not addressed here, be sure to communicate them to the Dafny team.

# How-to cookbook

## Background


# Pitfalls

# FAQs
## Dafny language

- ["Where do I put the reads clause?"](FAQReadsClause)

- ["I heard a rumor of datatypes extending traits coming in the pipeline. How will that work? Will we be able to use is and as with such types?"](FAQTraitsForDatatypes)

- ["What is the difference between a type and a newtype?"](FAQNewtype)

- ["Why can compiled modules contain but not import abstract modules?"() - TODO (9/1/2020)

- ["Why does Dafny need an assert in this example?"](FAQNeedsAssert)

- ["Why do I need a witness clause when I define a subset type or newtype?"](FAQWitness)

- ["Can I access the members of an outer module from its inner module?"(FAQNestedModule)

- ["What is `-` on bitvectors?"]() - TODO

- ["Is there a simple way to prove the termination of this recursive function?"]() - TODO 3/29/2021

- ["How do I make a singleton instance of a class for repeated later use?]() - TODO 3/30/2021

- ["Is there a way to write `if foo().equals(bar()) { x } else { y }` where `foo` and `bar` are methods?]() - TODO 3/31/2021

## Dafny tools

- ["Is there a Dafny style? and a Dafny linter (style checker and bad smell warnings)?] - TODO

- ["Is Dafny available as a library, to be called from other software?]() - TODO

- ["Is there a standard library for Dafny?"]() - TODO

## Dafny Infrastructure

- ["Why do I need to use an old Z3?"](FAQZ3)

- ["How do I ask a question or file a problem report or make a suggestion about Dafny?"() - TODO 

- ["Any plans to release the language server as a NuGet package? Seems like it’s not part of the Dafny release."]() - TODO

- ["How do I use Dafny with Brazil?"] -- TODO


# Common error messages

- ["'z3' cannot be opened because the developer cannot be verified.](ERROR_Z3)

- ["rbrace expected"](ERROR_Rbrace)

- ["Error: closeparen expected"](ERROR_CloseParen)

- ["Error: cannot establish the existence of LHS values that satisfy the such-that predicate"](ERROR_NoLHS)

- ["type parameter 0 (K) passed to type A must support no references"]() - TODO 12/29/2020

- ["I am getting a covariant type error and I am not sure how to resolve it."]() - TODO 3/25/2021
