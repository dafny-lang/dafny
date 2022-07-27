---
title: How-to and FAQ Guide for Dafny users
---

This page is the table of contents for a compendium of mini-lessons on Dafny programming idioms, how to accomplish various programming tasks in Dafny, how to fix error messages,
answers to FAQs or even just occasionally asked questions, and even information that you may not have asked yet, but you might.

These pages are not intended to be a reference manual or an organized tutorial for Dafny.

If you have questions that are not addressed here, be sure to communicate them to the Dafny team.

# FAQs
## Dafny language

- ["How do I format a string?] - TODO

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

- ["When I have multiple methods with the same extern value I get an error.  We need to do this to handle overloading in Java libraries.  Is there a workaround?"]() - TODO 4/1/2021

- [TODO: loop modifies problem] - 4/1/2021

- ["I can assert a condition right before a return, so why does the postcondition fail?](FAQFailingPost)

- ["I am getting a covariant type error and I am not sure how to resolve it."]() - TODO 3/25/2021

- ["How do I disambguate module names?](FAQModuleNames)

- ["A function seems to work just once. How do I get it to apply a bunch of times?"](FAQFunctionUnroll)

- ["Why is my import opened statement not working?"](FAQModuleImport)

- ["Is there a way to test that two types are the same?"](FAQTypeCompare)

- ["When a lemma has multiple ensures clauses, I’m finding that they interact, when I expected them to be independent.  For example, commenting out one of them can make another one not verify.  How should I think about this?"](FAQMultClauses)

- ["What is the difference between a lemma and a ghost method?"] - TODO (Stackoverflow, issue 2498)

- ["In an invariant, I want to say that once a boolean variable that starts false is set to true, it remains true forever.  Can I use old for this?"](FAQOld)

- ["When proving an iff (<==>), is there a nice way to prove this by proving each side of the implication separately without making 2 different lemmas?"](FAQIff)

- ["TODO: I’m having an issue with generics"] -- 6/5/2021

- ["Is there a way to do partial application for functions?"](FAQCurry)

- ["Why can a ghost const not be used as a witness? Does the compiler need to use the witness as an initial value?"](FAQGhostConstAsWitness)

- ["If I'm trying to prove a lemma in Dafny with a forall statement that needs help in the body ( {} ) of the lemma, how do I make an arbitrary variable (specifically of type string32 ) in the body of the lemma to help prove the forall statement?"] - TODO 6/18/2021

- ["Is there any difference between a method without a modifies clause and a function method with a reads this clause?  I know that the later you can use in expressions, but otherwise.  Is there anything the former can do that the later can’t, for example?"](FAQFunctionMethod)

- ["Dafny doesn’t like when a type and a module have the same name. How can I fix this?"](FAQNameConflict)

- ["Is there a way to prevent 'Warning: note, this forall statement has no body' from occurring? I have a forall loop with no body that results in the lemma verifying, but if I add a body (even an empty body) the lemma doesn't verify."](FAQNoBody)

- ["Is there a way to disable termination checks for recursive predicate definitions that I know to be logically consistent?"](FAQTermination)

- ["Is there a way to specify that all fields of an object, except a given one, don’t change?"](FAQModifiesOne)

## Dafny tools

- ["Is there a Dafny style? and a Dafny linter (style checker and bad smell warnings)?] - TODO

- ["Is Dafny available as a library, to be called from other software?]() - TODO

- ["Is there a standard library for Dafny?"]() - TODO

- ["Running Dafny on my program works, but trying to run Boogie on the bpl output from Dafny fails. What command-line arguments for Boogie am I missing?] - TODO

- ["When I try to compile and run the .jave file produced by Dafny, I get errors about missing packages. Where are they?"](FAQJava)

## Dafny Infrastructure

- ["Why do I need to use an old Z3?"](FAQZ3)

- ["How do I ask a question or file a problem report or make a suggestion about Dafny?"() - TODO 

- ["Any plans to release the language server as a NuGet package? Seems like it’s not part of the Dafny release."]() - TODO

- ["How do I use Dafny with Brazil?"] -- TODO


# How-to cookbook

# Pitfalls

# Common error messages

- ["'z3' cannot be opened because the developer cannot be verified."](ERROR_Z3)

- ["rbrace expected"](ERROR_Rbrace)

- ["closeparen expected"](ERROR_CloseParen)

- ["cannot establish the existence of LHS values that satisfy the such-that predicate"](ERROR_NoLHS)

- ["type parameter 0 (K) passed to type A must support no references"]() - TODO 12/29/2020

- ["a modifies-clause expression must denote an object or a set/iset/multiset/seq of objects (instead got map<int, A>)"](ERROR_ModifiesValue)

- ["name of datatype (String) is used as a function"]

- ["possible violation of function precondition for op(v)"](ERROR_FunctionPrecondition) - TODO - 5/24/2021

- ["type ? does not have a member IsFailure"] - TODO

- ["value does not satisfy subset constraints of ?"](ERROR_Covariance)

- ["function precondition might not hold"](ERROR_SeqComp)

- ["insufficient reads clause to invoke function"](ERROR_InsufficientReads) -- TODO 8/25/2021
