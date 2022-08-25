---
title: How-to and FAQ Guide for Dafny users
---

This page is the table of contents for a compendium of mini-lessons on Dafny programming idioms, how to accomplish various programming tasks in Dafny, how to fix error messages,
answers to FAQs or even just occasionally asked questions, and even information that you may not have asked yet, but you might.

These pages are not intended to be a reference manual or an organized tutorial for Dafny.

If you have questions that are not addressed here, be sure to communicate them to the Dafny team.

# FAQs
## Dafny language

- ["How do I format a string?"](FAQStringOutput)
- ["Where do I put the reads clause in a subset type?"](FAQReadsClause)
- ["Can datatypes extend traits?"](FAQTraitsForDatatypes)
- ["What is the difference between a type and a newtype?"](FAQNewtype)
- ["Why can compiled modules contain but not import abstract modules?"](FAQImportAbstractModule)
- ["Why does Dafny need an obvious assert?"](FAQNeedsAssert)
- ["Why do I need a witness clause when I define a subset type or newtype?"](FAQWitness)
- ["Can I access the members of an outer module from its inner module?"](FAQNestedModule)
- ["What is `-` on bitvectors?"](FAQBVNegation)
- ["Is there a simple way to prove the termination of a recursive function?"](FAQRecursiveTermination)

- ["What is the difference between a lemma and a ghost method?"](FAQGhostMethod)
- ["In an invariant, I want to say that once a boolean variable that starts false is set to true, it remains true forever.  Can I use old for this?"](FAQOld)
- ["When proving an iff (<==>), is there a nice way to prove this by proving each side of the implication separately without making 2 different lemmas?"](FAQIff)
- ["Is there a way to do partial application for functions?"](FAQCurry)
- ["Why can a ghost const not be used as a witness? Does the compiler need to use the witness as an initial value?"](FAQGhostConstAsWitness)
- ["How do I use forall statements and expressions in a lemma?"](FAQForall)
- ["Is there any difference between a method without a modifies clause and a function method with a reads this clause?  I know that the latter you can use in expressions, but otherwise.  Is there anything the former can do that the latter can’t, for example?"](FAQFunctionMethod)
- ["Dafny doesn’t like when a type and a module have the same name. How can I fix this?"](FAQNameConflict)
- ["Is there a way to prevent 'Warning: note, this forall statement has no body' from occurring? I have a forall loop with no body that results in the lemma verifying, but if I add a body (even an empty body) the lemma doesn't verify."](FAQNoBody)
- ["Is there a way to disable termination checks for recursive predicate definitions that I know to be logically consistent?"](FAQTermination)
- ["Is there a way to specify that all fields of an object, except a given one, don’t change?"](FAQModifiesOne)
- ["How do labels in preconditions work?"](FAQPreconditionLabels)
- ["Where are attributes documented?"](FAQAttribute)
- ["Is there a way to ask Dafny to die on its first verification failure?"](FAQDie)
- ["I can define a trait with some type parameters say trait `Test<A, B, C>`. When I use this trait is there a way to get Dafny to infer these types for me?"](FAQTypeInference)
- ["Does Dafny have monadic error handling?"](FAQMonadic)
- ["What is the `:-` operator?"](FAQElephant)
- ["How does `:-` work? I'm getting an unexpected failure."](FAQElephant)
- ["What is the meaning of and differences among `->`, `-->`, `~>`?"](FAQFunctionTypes)
- ["What is the difference between `function`, `method`, `function method`, and `function by method`?"](FAQFunctionMethodDiffs)
- ["Is it possible to restrict a type parameter to be a reference type? I see you can use T(!new) but I’m looking for the opposite."](FAQTypeParameterRestriction)
- ["A `seq` is an object reference, right?"](FAQReferences)
