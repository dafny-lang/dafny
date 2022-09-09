---
title: What is the meaning of and differences among `->`, `-->`, `~>`?
---

## Question

What is the meaning of and differences among `->`, `-->`, `~>`?

## Answer

These are all used in designating the type of functions; they are sometimes called _arrow types_.
In each case, `A -> B` is the type of a function taking an argument of type `A` and producing a value of type `B`;
The function argument types can be enclosed in parentheses, and if the number of arguments is not 1 or the argument is a tuple type, then the argument types must be enclosed in parentheses. For example,
`(A, B) -> C` is a type of function that takes two arguments; `((A, B)) -> C` takes as argument a 2-tuple.

The three symbols in the question denote different sorts of types of functions:
- `->` denotes a _total_ function that is independent of the heap; it may not have a `requires` clause (precondition) or a `reads` clause
- `-->` denotes a _partial_ function; it may have a precondition, but may not have a `reads` clause, and so it also is independent of the heap
- `~>` denotes a _partial_ and possibly _heap-dependent_ function; it may have `requires` and `reads` clauses

If a function is independent of the heap, it is useful to say so, either in its declaration or the type that describes it. The value returned by a heap-independent function depends only on its arguments and not on the program state; 
thus it is easier to reason about its properties. Working with heap-dependent functions is much more difficult than with heap-independent functions, so use `->` or `-->` if you can. And note that Dafny does not support polymorphic arrow types.
