---
title: How-to and FAQ Guide for Dafny users
---

This page is the table of contents for a compendium of mini-lessons on Dafny programming idioms, how to accomplish various programming tasks in Dafny, how to fix error messages,
answers to FAQs or even just occasionally asked questions, and even information that you may not have asked yet, but you might.

These pages are not intended to be a reference manual or an organized tutorial for Dafny.

If you have questions that are not addressed here, be sure to communicate them to the Dafny team.

# FAQs
## Dafny language

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

