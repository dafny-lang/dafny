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
- ["Where do I put the reads clause?"](FAQReadsClause)
- ["I heard a rumor of datatypes extending traits coming in the pipeline. How will that work? Will we be able to use is and as with such types?"](FAQTraitsForDatatypes)
- ["What is the difference between a type and a newtype?"](FAQNewtype)
- ["Why can compiled modules contain but not import abstract modules?"](FAQImportAbstractModule)
- ["Why does Dafny need an assert in this example?"](FAQNeedsAssert)
- ["Why do I need a witness clause when I define a subset type or newtype?"](FAQWitness)
- ["Can I access the members of an outer module from its inner module?"](FAQNestedModule)
- ["What is `-` on bitvectors?"](FAQBVNegation)
- ["Is there a simple way to prove the termination of a recursive function?"](FAQRecursiveTermination)
- ["How do I make a singleton instance of a class for repeated later use?](FAQSingleton)
- ["Is there a way to write `if foo().equals(bar()) { x } else { y }` where `foo` and `bar` are methods?](FAQMethodSequence)
- ["When I have multiple methods with the same extern value I get an error.  We need to do this to handle overloading in Java libraries.  Is there a workaround?"]() - TODO 4/1/2021
- [If I have an assertion about a class and a loop that doesn't mention (read, modify)  the class, why does dafny fail to establish the assertion after the loop?](FAQLoopModifies)
- ["I can assert a condition right before a return, so why does the postcondition fail?](FAQFailingPost)
- ["How can I combine sequences of different types?"](FAQSeqTrait)
- ["How do I disambiguate module names?](FAQModuleNames)
- ["A function seems to work just once. How do I get it to apply a bunch of times?"](FAQFunctionUnroll)
- ["Why is my import opened statement not working?"](FAQModuleImport)
- ["Is there a way to test that two types are the same?"](FAQTypeCompare)
- ["When a lemma has multiple ensures clauses, I’m finding that they interact, when I expected them to be independent.  For example, commenting out one of them can make another one not verify.  How should I think about this?"](FAQMultClauses)
- ["What is the difference between a lemma and a ghost method?"](FAQGhostMethod)
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
- ["How do I pattern match against a head and tail of a sequence or against a set?"](FAQMatchOnSet)
- ["How do I create a new empty map (or set or sequence)?"](FAQMepSetSeq)
- ["I have a module that exports a bunch of things. In another module I only need to use 1 thing. Is there a way to import only the thing that I want?"](FAQImportOneThing)
- [TODO - Sorting, iteration 12/1/2021]
- ["What is the difference between `modifies this`, `modifies this.x`, and ``modifies this`x``?](FAQModifiesThis)
- ["How does one define a record?"](FAQRecord)

## Dafny tools

- ["Is there a Dafny style? and a Dafny linter (style checker and bad smell warnings)?](FAQStyle)
- ["Is Dafny available as a library, to be called from other software?](FAQDafnyAsLibrary)
- ["Running Dafny on my program works, but trying to run Boogie on the bpl output from Dafny fails. What command-line arguments for Boogie am I missing?] - TODO
- ["When I try to compile and run the .jave file produced by Dafny, I get errors about missing packages. Where are they?"](FAQJava)
- ["Does Dafny verify methods in parallel?"](FAQParallel)
- ["Is there a doc generator for Dafny?"](FAQDocGenerator)
- [TODO 11/5- FAQ or ERROR?]
- ["Why does Dafny complain about `set i: int | Contains(i)`"] - TODO 1/13/2022
- ["What's the syntax for paths in include directives? How do they get resolved?"](FAQIncludes)
- ["Are there any useful tricks (e.g. z3 switches) to get better automation for nonlinear arithmetic (perhaps trading off other performance aspects)?"](FAQNonlinearArith)
- ["How do `{:split_here}` and `{:focus}` work to divide up a verification condition?"] - TODO - 1/7/2022
- ["How does one declare a type to have a "default" initial value, say a type tagged with {:extern}?'] - TODO - 1/10/2022
- ["A module A has names from an `import opened` or another module B, but if C imports A, it does not get those names. Please explain."](FAQImportOpened)
- ["It looks like, when compiling to C#, my print statements don't show up if I don't have \n at the end of the string."](FAQNewline)
- ["Are there functional alternatives to recursive calls that are more efficient or use less stack space?"] - TODO
- ["How do I read a file as a string?"](FAQReadFile)
- ["I can prove `!("a" <= "b")` but not `!("a" < "b")`, for `a` and `b` strings. Why is that?] 5/13/2022 TODO
- ["Can I ask dafny to not check termination of a function?"](FAQNoTermCheck)
- ["What does {:termination false} do on trait? It looks like it is required if I want to extend traits from other modules."](FAQTerminationFalse)
- TODO Refinement - 6/24/2022, 6/30/2022
- ["How do I make the dafny termination checker happy with this pattern of mutual recursion?"] - TODO 6/24/2022
- ["What is the easiest way to prove that a class instance is not an instance of a trait?"] - TODO 6/24/2022
- ["Is there a nice way to turn a set into a seq?"](FAQSetToSeq)
- ["How do I declare a default value for a parameter of a method or function?"] - TODO
- ["I just realized that a function I was compiling had a type-error inside a match case.  Instead of giving a compile error I was getting a redundant clause warning for the second case. What is the reason for this?"](FAQRedundantCase)
- ["Is there a way I can pass a variable with a generic type to a method with a concrete type?"] - TODO 7/15/2022
- ["How can ghost code call methods with side effects?"](FAQGhostSideEffects)

## Dafny Infrastructure

- ["Is there a standard library for Dafny?"](FAQStandardLibrary)
- ["Why do I need to use an old Z3?"](FAQZ3)
- ["How do I ask a question or file a problem report or make a suggestion about Dafny?"](FAQIssues)
- ["Any plans to release the language server as a NuGet package? Seems like it’s not part of the Dafny release."](FAQNuget)
- ["How do I use Dafny with Brazil?"] -- TODO
- ["What compiler target langages are in development?"](FAQCompileTargets)
- [ TODO - triggers 12/30/2021 ]
- ["Can classes appear in specs?"] = #yucca - 3/26/2021
- TODO Refinement types - #yucca 6/24/2022


# How-to cookbook
- ["How does one define a record?"] - TODO
- ["How do I create and use an iterator?] - TODO - 2/2/2022
- ["How do I manually run a program compiled to Java?"] TODO
- ["How do I manually run a program compiled to Go?"] TODO
- ["How do I manually run a program compiled to Javascript?"] TODO
- ["How do I manually run a program compiled to C#?"] TODO

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
- ["insufficient reads clause to invoke function"](ERROR_InsufficientReads) -- TODO 8/25/2021, 1/12/2022, 1/26/2022, 6/8/2022
- ["Cannot export mutable field 'x' without revealing its enclosing class 'A'"](ERROR_MutableField)
- ["this symbol not expected in Dafny"](ERROR_PostconditionLemma)
- [Prover error: Unexpected prover response (getting info about 'unknown' response): (:reason-unknown "Overflow encountered when expanding old_vector")](ERROR_ProverError1)
- ["Warning: File contains no code: ..."] TODO - no executable code
- ["Duplicate name of import: ..."](ERROR_DuplicateImportName)
- ["Warning: /!\ No terms found to trigger on."] TODO - #yucca 8/18/2021



Finished #dafny, #dafny-development, #yucca through 7/31

Check #yucca-compiler

https://broadcast.amazon.com/videos/394258
