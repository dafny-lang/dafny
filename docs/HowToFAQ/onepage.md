---
title: How-to and FAQ Guide for Dafny users (one page)
---

# How do I format a string?


## Question

How do I format a string?

## Answer

As of version 3.7.3, Dafny has no built-in or library capability to convert values to strings or to format them.
There is only the `print` statement that emits string representations of values to standard-out.

For now you will need to implement your own methods that convert values to strings, concatenating them to produce formatted strings.

# Where do I put the reads clause in a subset type?


## Question:

This example
```dafny
{% include_relative FAQReadsClause.dfy %}
```
generates this error:
```text
{% include_relative FAQReadsClause.txt %}
```
but there is no obvious place to put a `reads` clause.

## Answer:

There is no place for the `reads` clause because no such clause should be needed.
A type definition is not allowed to depend on a mutable field;
the predicate in the subset type must be pure.

The general idiom is to add a predicate, often named `Valid()`, to a class that
reads its fields and returns `true` if the class members are appropriately consistent. 
Then call `Valid()` in the pre- and post-conditions of methods and in
preconditions of functions and predicates. Here is an example:

```dafny
class A {
  var x: string
  var y: string
  predicate Valid() reads this {
    |x| == |y|
  }
}

method Test(a: A)
  requires a.Valid()
  requires a.x == ""
  modifies a
  ensures a.Valid()
{
  assert a.Valid(); // That's correct thanks to the precondition.
  a.x := "abc"; // Because |a.y| == 0, we broke the Valid() predicate
  assert !a.Valid(); // But that's ok.
  a.y := "bca";
  assert a.Valid(); // Now Dafny can prove this
  // The postcondition holds
}
```

The [`{:autocontracts}`]({../DafnyRef/DafnyRef#sec-attributes-autocontracts}) attribute can be helpful here.

Note that the idiom using `Valid()` above is similar to the use of class invariants in other 
specification languages.


# Can datatypes extend traits?


## Question:

I heard a rumor of datatypes extending traits coming in the pipeline. How will that work? Will we be able to use `is` and `as` with such types?

## Answer:

Yes, datatypes extending traits are coming (but not immediately).
The traits would need to be declared when the datatype is declared; the trait cannot be added later on.
`is` and `as` are possible.

# What is the difference between a type and a newtype?

## Question

One can define a _subset type_ like this
```
type int8 = x: int | -128 <= x < 128
```
and a newtype like this
```
newtype nint8 = x | -128 <= x < 128
```

What is the difference?

## Answer

In both cases, the values in the type are limited to the given range,
but a _newtype_ intends to define a whole new type that, although still based on integers and allowing integer operations,
is not intended to be mixed with integers.

This is evident in the allowed conversions, as shown in this example code:
```
{% include_relative FAQNewtype.dfy %}
```

The other important characteristic of `newtype`s is that they may have a different representation in the compilation target language.
Subset types are always represented in the same way as the base type.  But a newtype may use a different representation.
For example, the newtype defined above might use a `byte` representation in Java, whereas an `int` is a `BigInteger`.
The representation of a newtype can be set by the program author using the [`{:nativeType}`](../DafnyRef/DafnyRef#sec-nativetype) attribute.

# Why can compiled modules contain but not import abstract modules?


## Question

Why can compiled modules contain but not import abstract modules?

## Answer

The question refers to code like this:
```dafny
abstract module J {}

module K {
  abstract module JJ {}
  import J // ERROR
}
```
It is indeed the case that the abstract module `JJ` can be declared in non-abstract module `K` but the abstract module `J` is not permitted to be imported.
This discrepancy is the subject of a proposed change to Dafny rules (cf. [issue #2635](https://github.com/dafny-lang/dafny/issues/2635)).

In either cases, however, there are limits on what can be done with an abstract submodule.
It is first of all not compiled as part of the enclosing module. Thus it can only be used as the subject of refinement.

That feature is described in the remainder of this FAQ.

The enclosing module may declare an abstract module A and also a non-abstract module B that refines A.
A refining module import (`import D : C`) may only occur in an abstract module itself.

Generally speaking, suppose you have an underspecified module that is imported using ':', as in
```
abstract module Interface {
  function addSome(n: nat): nat
    ensures addSome(n) > n
}
abstract module Mod {
  import A : Interface
  method m() {
    assert 6 <= A.addSome(5);
  }
}
```
Here `A` is abstract because it stands for any concrete module that adheres to the interface declared in `Interface`
(note that the function `addSome` has no body). Consequently `Mod` must be abstract as well.
`Interface` is not compilable, but it actually does not need to be declared `abstract`.

Now we can implement a concrete version of `Interface`:
```
module Implementation {
  function addSome(n: nat): nat
    ensures addSome(n) == n + 1
  {
    n + 1
  }
}
```

Then we can implement the concrete module `Mod2` as a refinement of the abstract module `Mod`:
```
module Mod2 refines Mod {
  import A = Implementation
  ...
}
```
Here the module `Mod.A`, which is an unspecified refinement of `Interface` inside of `Mod`, is refined to be the concrete module
`Implementation` inside of `Mod2`, which is a refinement of `Mod`.

# Why does Dafny need an obvious assert?


## Question:

Why does Dafny need the assert in this example:
```
lemma Foo<T>(s: seq<T>, p: seq<T> -> bool)
  requires p(s[..|s|])
  ensures p(s)
{
  assert s[..|s|] == s;
}
```

## Answer

Not all facts about built-in types are built-in to Dafny.
Some, like this one, need to be asserted or otherwise provided as provable lemmas.

The reason is that trying to provide all seemingly obvious facts is both
a never-ending chase and, importantly, can lead to trigger loops, proof instabilities, and overall poor performance.
The importance of having proofs be stable and performance be generally fast outweighs building in all the properties of built-in types that might otherwise be reasonable.


# Why do I need a witness clause when I define a subset type or newtype?


## Question

Why do I need a witness clause in subtype definitions like
```
type A = s: int | Prime(x) witness 13
```

## Answer

Dafny generally assumes that types are non-empty; the witness is an example value that is in the type, demonstrating that the type is non-empty.

There are defaults for the `witness` clause, so you don't always have to have one. The default value is some zero-equivalent value: `0` for `int` based types, `0.0` for `real`-based types, 
empty sets, sequence and maps for those base types.

And, it is permitted to have possibly empty types by using a witness clause `witness *`, but there are restrictions on the use of possibly empty types.
For instance, a declaration of a variable with a possibly-empty type will need an initializer,
if that variable is ever used, because Dafny requires variables to be 'definitely assigned' before being used.

The Reference Manual contains a [discussion about witness clauses](../DafnyRef/DafnyRef#sec-witness-clauses).

# Can I access the members of an outer module from its inner module?


## Question

Can I access the members of an outer module from its inner module?
```dafny
{% include_relative FAQNestedModule.dfy %}
```

## Answer

No. The above example gives the error messages
```text
{% include_relative FAQNestedModule.txt %}
```

From a module you may access your own nested modules.
You may also access sibling modules and nested modules of sibling modules, but you need to import them.
That includes sibling modules of a module's own enclosing modules.
You may not access members of enclosing modules, including members declared at the global level (which are members of an implicit top-level module that includes everything in the program).

In general, there is a dependency order among modules: a module _depends on_ modules whose members it uses.
A module depends on its own nested modules.
A program cannot have circular dependencies: a module A cannot use members of module B if B (transitively) depends on A.

```dafny
module A {
  module B {
    const S1 := 10
  }
}

const S2 := 21
const S3 := C.D.A.B.S1 // OK

module C {
  module D {
    import A // OK - A is sibling of C
    import A.B // OK
    import E // OK - E is sibling of D
    import E.F // OK
    // import C // NOT OK - C is enclosing module
    // import EE = C.E // NOT OK -- can't access enclosing module
    // const X := S2 // NOT OK -- can't access top-level module
    const Y := B.S1 // OK - B is imported module
  }
  module E {
    module F {
    }
  }
}
```


# What is `-` on bitvectors?


## Question

What is `-` on bitvectors?

## Answer

The `-` operator for bit-vectors is subtraction or unary negation.
Unary negation, `- b` is equivalent to `0 - b`.
This is not the same as complement, which is written as `! b`.

For example, the `bv5` value equivalent to the natural number `13` is `01101`.
- The complement of this value is `10010`, which is `18`.
- The negation of this value is `10011`, which is `19`.

In 2's complement fixed-bit-width arithmetic, `-x` is `!x + 1`.

# Is there a simple way to prove the termination of a recursive function?


## Question

Is there a simple way to prove the termination of a recursive function?

Here is an example function:
```dafny
datatype Dummy = State1 | State2

function WalkState(str: string, s: Dummy): string {
  if str == [] then []
  else if s.State1? then WalkState(str[1..], Dummy.State2)
  else WalkState(str, Dummy.State1)
}
```

## Answer

In general, to prove termination of any recursive structure, one needs to declare a 
([well-founded](../DafnyRef/DafnyRef#sec-well-founded-orders)) measure that decreases on each iteration or recursive invocation;
because a well-founded measure has no infinitely decreasing sequences, the recursion must eventually terminate.
In many cases, Dafny will deduce a satisfactory (provable) measure to apply by default.
But where it cannot, the user must supply such a measure. A user-supplied measure is 
declared in a `decreases` clause. Such a measure is a sequence of expressions, ordered lexicographically by the
termination metric for each data type; the details of the ordering are 
explained in the [reference manual section on Decreases Clause](../DafnyRef/DafnyRef#sec-decreases-clause).

In the case of this example, the measure must be a combination of the length of the string, 
which decreases (and is bounded by 0) in the _else if_ branch and the state, 
creating a measure in which `Dummy.State1` is less than `Dummy.State2` and so decreases in the
final _else_ branch. So we can write
```dafny
datatype Dummy = State1 | State2

function WalkState(str: string, s: Dummy): string 
  decreases |str|, if s.State2? then 1 else 0
{
  if str == [] then []
  else if s.State1? then WalkState(str[1..], Dummy.State2)
  else WalkState(str, Dummy.State1)
}
```
which then proves without further user guidance.


# Is there a way to use methods within expressions?


## Question

Is there a way to use methods within expressions?

## Answer

No. Dafny distinguishes statements and expressions. Statements are permitted to update variables and fields (that is, have side-effects); expressions are not allowed to do so. In general, methods may have side-effects and so Dafny does not allow methods in expressions.
So you need to call each method in a statement of its own, using temporary local variables to record the results,
and then formulate your expression.

If the methods in question do not have side-effects, they can be rewritten as functions or 'function by method'
and then the syntax decribed above is fine.

# If I have an assertion about an object (of class type) and a loop that doesn't mention (read, modify) the object, why does dafny fail to establish the assertion after the loop?


## Question

If I have an assertion about an object and a loop that doesn't mention (read, modify) the class, 
why does dafny fail to establish the assertion after the loop?

## Answer

The short answer is that you need an appropriate combination of modifies clauses and 
loop invariants to prove assertions about the end result of a loop.

In Dafny's way of reasoning about a loop (which is typical of verifier systems), 
the loop invariant is the only thing you can assume at the top of every iteration. 
In other words, at the top of each loop iteration, it is as if all variables have 
arbitrary values, with the condition that the loop invariant is satisfied. 
Sometimes, the word _havoc_ is used to describe this: the verifier havocs all variables, 
that is, gives all variables arbitrary values, and then assumes the loop invariant.

If that’s all the verifier did, life would be a pain, because you’d have to write a
loop invariant about all variables in your program, even those that have nothing to do with the loop.
The verifier actually does better. Instead of havocing all variables, it suffices to havoc 
the assignment targets within the body of the loop, including anything that might be modified by methods called in the loop body. 
That is, the verifier uses a simple syntactic scan of the loop body to see which 
variables may possibly be assigned, and then it havocs only those variables. 
This saves users from having to write loop invariants about all other variables.
Only invariants about variables that are modified are needed.

What about the heap? For this purpose, the heap is considered to be one variable. 
So, the heap is either an assignment target of the loop or it isn’t. 
This means that if your loop body assigns to anything in the heap, the heap becomes an assignment target. 
Also, if the loop body allocates another object, that too is a change of the heap, 
so the heap becomes an assignment target. 
Furthermore, Dafny’s rule about a method is that a method is allowed to change the 
state of any object in the method’s modifies clause, 
and it is also allowed to allocate new objects and to modify their state. 
Therefore, if your loop body calls a method, then the heap may well become an assignment target.

So, then, does this mean your loop invariant needs to speak about everything in the heap whenever the heap is an assignment target of the loop?

Again, no. Loops in Dafny have `modifies` clauses, just like methods do (and just like for methods, 
newly allocated objects are implicitly included in those `modifies` clauses). 
It would be a pain to even have to write `modifies` clauses for every loop, 
so if a loop does not have an explicit `modifies` clause, Dafny implicitly attaches 
the `modifies` clause of the enclosing method (or of the enclosing loop, in the case of nested loops). 
This default behavior turns out to be right in almost all cases in practice, 
which is why you normally don’t have to think about this issue.

But when it is not, you need to be explicit about the `modifies` clause and the loop invariants. 
In particular
- write a `modifies` clause for the loop that includes all objects whose fields might be 
assigned in the loop body (or listed in the modifies clauses of anything the loop body calls)
- then write a loop invariant that includes assertions about any variable that is listed in the modifies clause
or is an assignment target in the loop body. 
Very typically, the invariant will give a value for each havoced variable showing its relationship to the loop index.

For example, a loop that sets the elements of an array to some initial value might look like this:
```dafny
method init(a: array<int>) 
  modifies a
  ensures forall j | 0 <= j < a.Length :: a[j] == j
{
  var i := 0;

  while i < a.Length
    modifies a
    invariant 0 <= i <= a.Length && forall j | 0 <= j < i :: a[j] == j
  {
    a[i] := i;
    i := i + 1;
  }
}
```

Note the following points:
- The method specifies that it might modify the elements of the array `a`.
- The loop says that it modifies the same array. 
In fact that modifies clause could be omitted
because it would be inherited from the enclosing context.
- The loop also modifies `i`, but as `i` is a local variable, it need not be listed in the modifies clause.
- The loop also has an invariant, which has two conjuncts:
   - One conjunct talks about the local variable `i`. Even though `i` is not in the modifies clause 
    it is an assignment target, so we need to say what is known about it (prior to the loop test).
   - The other conjunct talks about the elements of `a`, which depend on `i`, 
    that is, on how many iterations of the loop have been executed.
- After the loop, Dafny uses the loop invariant and the negation of the loop guard to conclude `i == a.Length`, and from that and the invariant, Dafny can prove the method's postcondition.

Even when Dafny can infer an appropriate modifies clause, it does not infer loop invariants, so the user always needs to supply those. 

Here is another example:
```dafny
class Counter {
  var n: nat
}

// print "hello" c.n times and then increment c.n
method PrintAndIncrement(c: Counter)
  modifies c
  ensures c.n == old(c.n) + 1
{
  for _ := 0 to c.n
    // To verify this method, the loop needs one of the following two lines:
    invariant c.n == old(c.n)
    modifies {} // empty modifies clause
  {
    PrintHello();
  }
  c.n := c.n + 1;
}

method PrintHello() {
  print "hello\n";
}
```
The for-loop can be specified and the whole method verified in two different ways.

First, suppose we do not include a modifies clause in the loop specifications of the loop.
Then dafny will use the enclosing modifies clause, which allows changing the
state of `c`. In order for the method body to know that the loop has not 
changed `c.n`, the loop needs the invariant `c.n == old(c.n)`.

Alternatively, the loop can specify its own modifies clause,
`modifies {}`, saying it modifies nothing. Then it follows directly that
`c.n` does not change in the loop, so no invariant is needed to carry out the proof.

# I can assert a condition right before a return, so why does the postcondition fail to verify?


## Question

I can assert a condition right before a return, so why does the postcondition fail to verify?

## Answer

There can be lots of reasons why a postcondition might fail to verify, but if you can prove the same predicate just before a return, 
a typical reason is that there are other exit paths from the method or function. There might be other `return` statements, but a
harder to spot exit path is the `:-` let-or-fail assignment.
Here is a sketch of that kind of problem:

```dafny
include "library/Wrappers.dfy"

method test(MyClass o) returns (r: Wrappers.Result<int>)
  modifies o;
  ensures o.ok == true;
{
  o.ok := true;
  o.data :- MyMethod(o);
  assert o.ok;
  return;
}
```
(This example uses the `Result` type from the [standard library](https://github.com/dafny-lang/libraries/blob/master/src/Wrappers.dfy). The `include` directive in the example requires that you have a copy of the standard library in `./library`.)

This method can exit either through the `return` at the end or through the failure return if a failure value is returned
from `MyMethod`. That return happens before the `assert` that is intended to do a pre-check of the postcondition; depending
on the action of `MyMethod`, the target predicate may not be always true.
  

# How can I combine sequences of different types?


## Question

How can I combine sequences of different types?

## Answer

It depends on the types. If the different types are subset types of a common base type, you can make a combined list of the base type. Similarly if the two types are classes (or traits) that extend a common trait, then you can combine sequences into a sequence of that trait. And since all classes extend the trait `object`, that can be the common type.

Here is some sample code:
```dafny
trait T {}
class A extends T {}
class B extends T {}

method m() {
  var a: A := new A;
  var sa: seq<A> := [ a ];
  var b := new B;
  var sb : seq<B> := [b ];
  var st : seq<T> := sa + sb;
  var so : seq<object> := sa + sb;
}
```

In fact, Dafny will generally infer a common type for you in the case of sequence concatentation.

# How do I disambiguate module names?


## Question

How do I disambiguate module names in an example like this:
```dafny
{% include_relative FAQModuleNames0.dfy %}
```

## Answer

There is no direct syntax to do what is wanted here.
If you have control of the names, perhaps some renaming or moving the top-level `util` to be a sub-module of another module.
If this structure cannot be changed, then the following somewhat ugly code is a work-around:
```dafny
{% include_relative FAQModuleNames.dfy %}
```

There is discussion of defining syntax that names the top-level module, which would make an easy way to solve the above problem. See [this issue](https://github.com/dafny-lang/dafny/issues/2493).

# A function seems to work just once. How do I get it to apply a bunch of times?


## Question

A function seems to work just once. How do I get it to apply a bunch of times?
Here is an example:
```
{% include_relative FAQFunctionUnroll0.dfy %}
```

The latter two lemmas will not prove without uncommenting the application of the lemma for one less iteration.
How can I get this to prove automatically?

## Answer

Function bodies are transparent. That is, when there is a call to a function in Dafny code, the body of the function
is available for reasoning about the effect of the function. But for recursive functions, it generally only does this once or twice, as that is 
usually sufficient to form an inductive proof. And always unrolling multiple times can reduce performance.

You can request that Dafny unroll a function multiple times by using the `{:fuel}` attribute.
The value of the attribute is the number of times the function will be unrolled. This is still a fixed upper limit,
but it does the trick in this case:
```
{% include_relative FAQFunctionUnroll1.dfy %}
```

A function will also keep unrolling if it has an argument that is a literal and that argument decreases
on each recursive call. So for this example we can write a helper function that takes a `nat` argument
and give it a literal value that tells it how much to unroll.
```
{% include_relative FAQFunctionUnroll2.dfy %}
```
With this solution, the number of unrollings can be set at the call site, rather than in the function definition.

[This paper](https://www.microsoft.com/en-us/research/publication/computing-smt-solver/) gives some technical insight into how recursive functions are handled in situations like these examples.


# Why do nested modules not see the imports of their enclosing modules?


## Question

Why is my import opened statement not working in the following example:
```
{% include_relative FAQModuleImport.dfy %}
```

## Answer

Although nested modules are nested inside other modules, they should really be thought of as their own module.
There is no particular benefit to module `A.B` from being nested inside module `A`  none of the declarations of `A` are visible in `B` other than the names of sibling modules of `B`.
The benefit is to module `A`, for which the nested module `B` is a namespace that can group some related declarations together.

Accordingly, if you want some names from another module to be available within a submodule, you must import that directly in the submodule.
The example above becomes this:
```
{% include_relative FAQModuleImport1.dfy %}
```

# Is there a way to test that two types are the same?


## Question

Is there a way to test that two types are the same, as in this exmple:
```
{% include_relative FAQTypeCompare.dfy %}
```

## Answer

No. Types are not first-class entities in Dafny. There are no variables or literals of a type `TYPE`.
There is a type test for reference types, namely `is`, but that is not a strict type equality but a
test that the dynamic type of a reference object is the same as or derived from some named type.

# When a lemma has multiple ensures clauses, I’m finding that they interact, when I expected them to be independent.  For example, commenting out one of them can make another one not verify.  How should I think about this?


## Question

When a lemma has multiple ensures clauses, I’m finding that they interact, when I expected them to be independent.  For example, commenting out one of them can make another one not verify.  How should I think about this?

## Answer

Multiple ensures clauses, such as `ensures P ensures Q ensures R` is equivalent to the conjunction, in order, of the ensures predicates: `ensures P && Q && R`.
The order is important if an earlier predicate is needed to be sure that a later one is well defined. For example,
if `a` is an `array?`, the two predicates in `ensures a != null ensures a.Length > 0`
must be in that order because `a.Length` is well-defined only if `a != null`.

In addition, sometimes one ensures clause serves as an intermediate reasoning step for the next one. Without the earlier clause, Dafny can have trouble proving the second one, even though it is valid.
With the first predicate as an intermediate step, the second is then more easily proved.

This order dependence of postconditions is also the case for preconditions and loop invariants

# What is the difference between a lemma and a ghost method?


## Question

What is the difference between a lemma and a ghost method?

## Answer

A `lemma` is a `ghost method` that does not have a `modifies` clause. Lemmas also do not typically return results.
However, in most places where a lemma is used, it must be declared as a lemma. For example the lemma call that can be part of an expression must call a method that is declared to be a lemma, not a ghost method.

A lemma may also be called as a statement in the body of a method, but here a ghost method is allowed as well, so either can be used.

# In an invariant, I want to say that once a boolean variable that starts false is set to true, it remains true forever.  Can I use old for this?


## Question

In an invariant, I want to say that once a boolean variable that starts false is set to true, it remains true forever.  Can I use old for this?

## Answer

Almost but not quite. `old` gives you the value of an expression in the method's pre-state or at given label. 
Equivalently. you can stash the value of an expression at some point in the control flow in some temporary (even ghost) variable.
Then you can state a predicate saying "if the expression was true at that specific point, then it is still true now when I am testing it".

But that is not quite saying "once an expression becomes true, it stays true".
For that you need a more complicated solution:
- declare a ghost variable `nowTrue`, initialized to `false`
- at every location where the expression (call it `e`) is set, 
   - first test its new value: `if nowTrue && !e { FAILURE }`
   - and then set the ghost value `nowTrue := nowTrue || e;`

# When proving an iff (<==>), is there a nice way to prove this by proving each side of the implication separately without making 2 different lemmas?


## Question

When proving an iff (<==>), is there a nice way to prove this by proving each side of the implication separately without making 2 different lemmas?

## Answer

Here are two ways to prove `A <==> B`:

```
if A {
  // prove B...
}
if B {
  // prove A...
}
```
Another way is
```
calc {
  A;
==
  // ...
==
  B;
}
```

# Is there a way to do partial application for functions?


## Question

Is there a way to do partial application for functions in Dafny?

## Answer

Given
```
function f(i: int, j: int): int {...}
```
one can create a new partially-evaluated function, say evaluating the first argument at `2`, by writing the lambda expression `k => f(2,k)`.
But note that this does not do any evaluation, partial or not. It merely defines a new function `f'` of one argument, such at `f'(k)` is `f(2,k)`.

Dafny does not permit the syntax `f(2)` as a shorthand for `k => f(2,k)`.

# Why can a ghost const not be used as a witness? Does the compiler need to use the witness as an initial value?


## Question

Why can a ghost const not be used as a witness? Does the compiler need to use the witness as an initial value?

## Answer

A type can be
- auto-initializing (which means the compiler knows of a value of the type)
- nonempty (which means there is a value of the type, but the compiler might not know it)
- possibly empty (neither or the above is true)

To show a type is auto-initializing, you may need to provide a witness clause. The expression given in the witness clause must be compilable.
To just show a type is nonempty, you can use a ghost witness clause. It takes a ghost expression, so you should be able to use your ghost const here.
If you don’t care about either, you can say `witness *`, which makes the type be treated as possibly empty.

When declaring generic types, one can use _type characteristics_ to indicate any restrictions on the types that may be substituted for a type parameter.
For example, writing `class A<T(0)>` says that types substituted fo `T` must be auto-initializing;
writing `class A<T(00)>` says that such types must be non-empty.

# How do I use `forall` statements and expressions in a lemma?


## Question

If I'm trying to prove a lemma in Dafny with a `forall` statement that needs help in the body (`{}`) of the lemma, how do I make an arbitrary variable in the body of the lemma to help prove the `forall` statement?

## Answer

Note that there is a difference between a `forall` expression, which is a universally quantified formula, and a `forall` statement, which is used to establish the truth of a universally quantified formula. To do what you want to do, write:
```dafny
lemma MyLemma()
  ensures forall s :: P(s) ==> Q(s)
{
  forall t | P(t)
    ensures Q(t)
  {
    // Here, t is in scope, and P(t) is assumed.
    // Your task here is to prove Q(t) for this particular t.
  }
  // Here, you get to assume "forall t :: P(t) ==> Q(t)"
}
```

The `forall` in the ensures is an expression and the `forall` in the body of the lemma is a statement.

This use of the `forall` statement is what logicians call “universal introduction”.

Note the slight difference in syntax between the `forall` expression and `forall` statement.
Although Dafny tries to make the syntax of these sorts of things as similar as possible between expressions and statements, there are some differences. 
The following Dafny Power User note may be helpful in understanding the syntax: [Dafny Power User: Statement vs. Expression Syntax](http://leino.science/papers/krml266.html).

# Is there any difference between a method without a modifies clause and a function with a reads this clause?  I know that the latter you can use in expressions, but otherwise, is there anything the former can do that the latter can’t, for example?


## Question

Is there any difference between a method without a `modifies` clause and a function method with a `reads this` clause?  I know that the latter you can use in expressionse.  Is there anything the former can do that the latter can’t, for example?

## Answer

Compared to a function, a method can
- allocate objects and arrays (`new`)
- use non-determinism
- use loops
- have multiple outputs
- read anything in the heap

# Dafny doesn’t like when a type and a module have the same name. How can I fix this?


## Question

Dafny doesn’t like when a type and a module have the same name. How can I fix this?
```
{% include_relative FAQNameConflict.dfy %}
```
produces
```
{% include_relative FAQNameConflict.txt %}
```

## Answer

The problem is that in the `Test` module, the name `Result` is both a module name and a datatype name.
The module name takes precedence and so the resolution error happens.
(Despite the error message, modules never have type arguments.)

This situation can be fixed two ways. First, write `Result.Result` to mean the datatype. Or second, 
import the module with a new name, such as `import opened R = Result`. Then inside module Test, there is
the name `R` for a module and the name `Result` for the datatype. The following code shows both these options.
```
{% include_relative FAQNameConflict1.dfy %}
```

# "Is there a way to prevent 'Warning: note, this forall statement has no body' from occurring? I have a forall loop with no body that results in the lemma verifying, but if I add a body (even an empty body) the lemma doesn't verify."


## Question

Is there a way to prevent "Warning: note, this forall statement has no body" from occurring? I have a forall loop with no body that results in the lemma verifying, but if I add a body (even an empty body) the lemma doesn't verify.

## Answer

The Dafny verifier allows you to omit the body of various constructs. For example, if you write a method without a body, the verifier will gladly check calls to the method against that specification (after checking the well-formedness of the method specification). This is nice, because it lets you write the specification of a method and then start using it in other places, only to later return to filling in the body of the method.

The verifier is happy with such a body-less thing, but the once verification is done and you’re asking Dafny to compile your program, the compiler will complain, because it doesn’t know how to synthesize code for the method specification you wrote.

You can also do this with loops. For example, you can write
```dafny
while i < N
  invariant s == i * (i + 1) / 2
```
and not give a body. Again, the verifier is happy and will gladly check the rest of the code that follows the loop. This allows you to write down the loop invariant and make sure that the code after the loop is fine, only to later return to filling in the loop body.

If you leave off the body of a loop, Dafny will gently remind you of this by giving a warning like “this loop statement has no body”.

The forall statement is an aggregate statement. It simultaneously performs something for all values of the bound variables. In proofs, the forall statement is used as the counterpart of what logicians call “universal introduction”. In code, the forall statement has various restrictions, and is typically used to initialize all elements of an array.
The forall statement can also be declared without a body. Again, the verifier is happy to reason about its use, but the compiler would complain that there’s no body.

So, in the end, you do need to prove a body for your forall statements. You’ll have to make sure the body establishes the postcondition of the forall statement.

And even for functions and lemmas without bodies, even though the verify does not complain, they are unproved assumptions in your program.

# Is there a way to disable termination checks for recursive predicate definitions that I know to be logically consistent?


## Question

Is there a way to disable termination checks for recursive predicate definitions that I know to be logically consistent?

## Answer

Well, first of all, be careful about thinking things like "I know this to be logically consistent". Verifiers exist to check our human tendency to hand-wave over questionable assumptions.

That said, you can do something like this:

```dafny
predicate P(x: int, terminationFiction: int)
  decreases terminationFiction
{
  assume 0 < terminationFiction;
  P(x, terminationFiction - 1)
}
```

That may cause some quantification triggering problems and may need an axiom like
```
forall x,j,k:int :: P(x, j) == P(x, k)
```

It can also help to manually instantiate an axiom to avoid triggering issues:
declare the axiom like this:
```dafny
lemma {:axiom} PSynonym(x: int, j: int, k: int)
  ensures P(x, j) == P(x, k)
```
and then call the lemma as needed.

# Is there a way to specify that all fields of an object, except a given one, don’t change?


## Question

Is there a way to specify that all fields of an object, except a given one, don’t change?

## Answer

Instead of writing `modifies this` or `modifies o`, you can write ``modifies this`f`` (equivalently ``modifies `f``)
or ``modifies o`f``
to indicate that just the field `f` of `this` or `o`, respectively, may be assigned to.

# How do labels in preconditions work?


## Question

How do labels in preconditions work?

## Answer

```dafny
{% include_relative FAQPreconditionLabels.dfy %}
```

In the code example above, the precondition `x == 0` is labeled with `Zero`.
Unlabeled preconditions are assumed at the beginning of a method body,
but labeled preconditions are not. Labeled preconditions are only assumed
when they are explicitly `reveal`ed. So in the example, the assert in method 
`M1` cannot be proved because the fact `x < 10` is not known. 
In method `M2`, that fact is made known by the `reveal` statement, and so here
the `assert` can be proved. The effect of the `reveal` is just as if an assumption were
made at the point of the `reveal` statement.

Note that if the `reveal` statement is in a `by`
block of an `assert by` statement, then the revealing is limited to the proof of the 
corresponding `assert`.

These same rules apply to labeled `assert` statements.

There is an expanded discussion in section 7 of [_Different Styles of Proofs_](http://leino.science/papers/krml276.html).

# Where are attributes documented?


## Question

Where are attributes documented? Why does my attribute not seem to make a difference?

## Answer

In general, attributes are documented in a chapter of the [reference manual](../DafnyRef/DafnyRef#sec-attributes); some are also documented in the sections in which the language feature for which they are relevant is described.
However, at present not all of them are documented.

Some projects with forks of Dafny may introduce attributes of their own.
Keep in mind, that any attributes not recognized by Dafny are silently ignored, to allow for such extension.

# Is there a way to ask Dafny to die on its first verification failure?


## Question

Is there a way to ask Dafny to die on its first verification failure?

## Answer

No. At least as of version 3.7.3.

# I can define a trait with some type parameters say trait Test<A, B, C>. When I use this trait is there a way to get Dafny to infer these types for me?


## Question

I can define a trait with some type parameters say trait `Test<A, B, C>`. When I use this trait is there a way to get Dafny to infer these types for me?

## Answer

Type inference, though quite extensive in its effect, only works within the bodies of functions and methods.
Types in signatures and actual values for type parameters need to be written explicitly.

When type inference is used (within a body), types are determined by how they are used, not just be initializing
expressions. So the inferred type in a declaration may depend on code that appears textually after the declaration.
Here is some example code:
```dafny
class C<X(0)> {
  static method M() returns (x: X) {
  }

  method P() {
    var x0 := M();        // type of x0 inferred to be X, from M()'s signature
    var x1 := C<int>.M(); // type of x1 inferred to be int
    var x2: int := C.M(); // M() instantiated with int

    var x3 := C.M();      // error: type of x3 is underspecified
    var x4: int := M();   // error: M() instantiated with X, but x4 has type int
  }
}
```

# Does Dafny have monadic error handling?


## Question

Does Dafny have monadic error handling?

## Answer

Yes.

In particular, see the section of the reference manual on [Update with Failure statements](../DafnyRef/DafnyRef#sec-update-failure).
The (draft) standard library includes [some types needed for error handling](https://github.com/dafny-lang/libraries/blob/master/src/Wrappers.dfy).

You can define your own monadic error type by following examples in the RM and the draft library. A simple case is
```dafny
datatype Outcome<T> =
            | Success(value: T)
            | Failure(error: string)
{
  predicate IsFailure() {
    this.Failure?
  }
  function PropagateFailure<U>(): Outcome<U>
    requires IsFailure()
  {
    Failure(this.error) // this is Outcome<U>.Failure(...)
  }
  function Extract(): T
    requires !IsFailure()
  {
    this.value
  }
}
```

# What is the `:-` operator? How does it work?


## Question

What is the `:-` operator? How does it work?

## Answer

This operator is called the _elephant operator_ (because it has a trunk).
It is used to write code that exits on failure (much like exceptions in other programming languages or the ? operator in Rust).
The topic is discussed at length in
the section of the reference manual on [Update with Failure statements](../DafnyRef/DafnyRef#sec-update-failure).

In brief, Dafny permits methods to return values of _failure-compatible_ types. If the result of a method is being assigned to a variable with the `:-` operator and the result is a failure, then the method exits immediately, with the failure being propagated to the calling method.

# What is the `:-` operator? How does it work?


## Question

What is the `:-` operator? How does it work?

## Answer

This operator is called the _elephant operator_ (because it has a trunk).
It is used to write code that exits on failure (much like exceptions in other programming languages or the ? operator in Rust).
The topic is discussed at length in
the section of the reference manual on [Update with Failure statements](../DafnyRef/DafnyRef#sec-update-failure).

In brief, Dafny permits methods to return values of _failure-compatible_ types. If the result of a method is being assigned to a variable with the `:-` operator and the result is a failure, then the method exits immediately, with the failure being propagated to the calling method.

# What is the meaning of and differences among `->`, `-->`, `~>`?


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

# What is the difference between `function`, `method`, `function method`, and `function by method`?


## Question

What is the difference between `function`, `method`, `function method`, and `function by method`?

## Answer

The names of these alternatives will be changing between Dafny 3 and Dafny 4:

- `function` (`function method` in Dafny 3) -- is a non-ghost function
- `ghost function` (`function` in Dafny 3) -- is a ghost function
- _function by method_ is a ghost function with an alternate compilable (non-ghost) method body (cf. [the reference manual section on function declarations](../DafnyRef/DafnyRef#sec-function-declarations))
- `method` declares a non-ghost method
- `ghost method` declares a ghost method, though this is almost always done using a `lemma` instead

Note that
- Methods may have side effects but may not be used in expressions.
- Functions may be used in expressions but may not have side effects.
- Methods do not have reads clauses; functions typically do.
- Non-ghost methods and non-ghost functions may not be used in ghost code.

# Is it possible to restrict a type parameter to be a reference type? I see you can use T(!new) but I’m looking for the opposite.


## Question

Is it possible to restrict a type parameter to be a reference type? I see you can use `T(!new)` but I’m looking for the opposite.

## Answer

No. The only restrictions available (as of version 3.7.3) are
- `T(==)` - type supports equality
- `T(0)` - type is auto-initializable
- `T(00)` - type is non-empty
- `T(!new)` - type may **not** be a reference type or contain a reference type

See the [appropriate section of the reference manual](../DafnyRef/DafnyRef#sec-type-parameter-variance) for more information.

# A `seq` is an object reference, right?


## Question

A `seq` is an object reference, right?

## Answer

No. Types in Dafny are either heap-dependent (reference) types or strict value-types. Built-in types are typically value types.
Value types are heap independent, though they may be stored in the heap as part of an object.

Value types include `bool`, `int`, `char`, `real`, `ORDINAL`, datatypes and co-datatypes, arrow types, bit-vector types, `seq`, `set`, `iset`, `multiset`, `map`, `imap`, `string`, tuple types,  and subset or newtypes with value type bases.

Reference types are classes, traits, arrays, and iterators.

The values of value types are immutable; new values may be computed but are not modified. Integers are a good mental
model for value types, but in Dafny, datatypes, sequences, sets, and maps are also immutable values. 
Note that though the values of these types are immutable,
they may contain instances of reference types (which might be mutable).

# How do I pattern match against a head and tail of a sequence or against a set?


## Question

How do I pattern match against a head and tail of a sequence or against a set?

## Answer

You can't. Match [expressions](../DafnyRef/DafnyRef#sec-match-expression) and [statements](../DafnyRef/DafnyRef#sec-match-statement) operate on `datatype` values and not on other Dafny types like sets, sequences, and maps. If statements, perhaps with [binding guards](../DafnyRef/DafnyRef#sec-binding-guards), may be an alternative.


# How do I create a new empty map (or set or sequence)?


## Question

How do I create a new empty map (or set or sequence)?

## Answer

An empty sequence is denoted by `[]`, an empty set by `{}`, an empty multiset by `multiset{}`,  and an empty map by
`map[]`. The type of the empty collection is typically inferred from its subsequent use.

The various operations on values of these types are described [in the reference manual section on Collection Types](../DafnyRef/DafnyRef#sec-collection-types).

# I have a module that exports a bunch of things. In another module I only need to use 1 thing. Is there a way to import only the thing that I want?


## Question

I have a module that exports a bunch of things. In another module I only need to use 1 thing. Is there a way to import only the thing that I want?

## Answer

The short answer is: use an export set.

Here is an example. Suppose you have this code:
``` dafny
module A {
  export JustJ reveals j
  const i: int := 64
  const j: int := 128
}
module B {
  //import opened A // imports both i and j
  import opened A`JustJ // just imports j
}
```
The `export` directive in module `A` just exports the name `j` in the export set `JustJ`.
So then you can import just `j` in `B` by importing ``A`JustJ``.

You can create as many export sets as you like, for different contexts.
See the details [here](../DafnyRef/DafnyRef#sec-export-sets-and-access-control).

This feature does put the onus of defining the groups of exportable names on the supplying module.
Your question asks for such control by the receiving module. The best course for the receiving
module is to not use `import opened` and just use a qualified name for the one thing that is being used from the
supplying module.

# What is the difference between modifies this, modifies this.x, and modifies this`x?


## Question

What is the difference between `modifies this`, `modifies this.x`, and ``modifies this`x``?

## Answer

A `modifies` clause for a method lists object references whose fields may be modified by the body of the method.
- `this` means that all the fields of the `this` object may be modified by the body
- `this.x` (where `x` is a field of `this` and has some reference type) means that fields of `x` may be modified (but not the field `x` itself of `this`)
- ``this`x`` means that just the field `x` of `this` may be modified (and not any other fields, unless they are listed themselves)

If there are multiple items listed in the modifies clause, the implicit clause is the union of all of them.
More on framing (`modifies` and `reads` clauses) can be found in the [reference manual section on Framing specifications](../DafnyRef/DafnyRef#sec-frame-expression).

# How does one define a record?


## Question

How does one define a record?

## Answer

The Dafny `datatype` feature lets you define simple or complex records, including recursive ones.

A simple enumeration record might be defined as
```dafny
datatype ABCD = A | B | C | D
```
Variables of type `ABCD` can take one of the four given values.

A record might also be a single alternative but with data values:
```dafny
datatype Date = Date(year: int, month: int, day: int)
```
where a record instance can be created like `var d := Date(2022, 8, 23)` and componenents retrieved like `d.year`.

There can be multiple record alternatives each holding different data:
```dafny
datatype ABCD = A(i: int) | B(s: string) | C(r: real) | D
const a: ABCD := A(7)
const b: ABCD := B("asd")
const c: ABCD := C(0.0)
const d: ABCD := D
```

You can determine which alternative a record value is with the built-in test functions: with the definitions above, `a.A?` is true and `b.C?` is false. And you can extract the record alternative's
data: in the above `a.i` is well-defined if `a.A?` is true, in which case it has the value `7`.

There is more description of datatypes [here](../DafnyRef/DafnyRef#sec-algebraic-datatype).

# "What does `forall v :: v in vals ==> false` evaluate to if `vals` is non-empty?"


## Question

What does `forall v :: v in vals ==> false` evaluate to if `vals` is non-empty?
Should it be false? I’m having some problem proving the last assertion in Dafny.

```dafny
assert vals != [];
assert MatchingResult() == (forall v :: v in vals ==> false);
assert !MatchingResult();
```

## Answer

The problem here is the trigger on the quantification expression.
Dafny sees the `forall` quantifier but uses it only when there is a `v in vals` fact in the context for some v (this is what the annotation on the forall in the VSCode IDE means: Selected triggers: {v in vals}).  So until you give it a concrete fact to "trigger" on, it doesn't use your quantifier.

It is not recommended that users insert triggers in their Dafny code. Rather, it is better to reorganize the 
quantification expressions to make the desired trigger more obvious to the Dafny tool.
Here are two references that explain triggers in more detail:
- [A wiki page on triggers](https://github.com/dafny-lang/dafny/wiki/FAQ#how-does-dafny-handle-quantifiers-ive-heard-about-triggers-what-are-those)
- [Pages 2--4 of this paper](https://pit-claudel.fr/clement/papers/dafny-trigger-selection-CAV16.pdf)

# "Why does Dafny complain about this use of a set constructor: `set i: int | Contains(i)`?"


## Question

Why does Dafny complain about this use of a set constructor: `set i: int | Contains(i)`?
Here is an example:
```dafny
module test {

  ghost const things: set<int>

  predicate Contains(t: int) 
  {
    t in things
  }

  function ThisIsOk(): set<int> {
    set i: int | i in things && i > 0
  }

  function ThisIsNotOk(): set<int> {
    set i: int | Contains(i) && i > 0
  }

}
```

which produces the error "the result of a set comprehension must be finite, but Dafny's heuristics can't figure out how to produce a bounded set of values for 'i'".

## Answer

In constructing a `set`, which must be finite, Dafny must prove that the set is indeed finite.
When the constructor has `i in things` inlined, Dafny can see that the set of values of `i` for which the predicate is true can be no larger than `things`, which is already known by declaration to be 
a finite set. However, when the predicate is `Contains`, Dafny cannot in general see that fact.
The Dafny's heuristic for determining that the constructor is producing a finite set does not
inspect the body of `Contains` even though that is a transparent function. Note that if the constructor and the return type of `ThisIsNotOK` is made `iset`, Dafny does not complain.

An alternate general way to refine a set is given by this example:
```dafny
module test {

  ghost const things: set<int>

  function RefineThings(condition: int -> bool): set<int>
  {
    set t: int | t in things && condition(t)
  }

  function ThisIsOk(): set<int> {
    set i: int | i in things && i > 0
  }

  function ThisIsOkAgain(): set<int> {
    RefineThings(i => i > 0)
  }
}
```

# What's the syntax for paths in include directives? How do they get resolved?


## Question

What's the syntax for paths in include directives? How do they get resolved?

## Answer

An include directive  is the `include` keyword followed by a string literal (in quotes).
The string is a conventional file path for the OS on which you are running and is the full file name with extension.
The filepath can be either absolute or relative; if relative, it is relative to the current working directory 
(i.e., the result of `pwd` on Linux).

As of version 3.7.3, there is no "include path" that might allow paths relative to other locations, but it is a feature request.

# How do `{:split_here}` and `{:focus}` work to divide up a proof?


## Question

How do `{:split_here}` and `{:focus}` work to divide up a proof?

## Answer

Verifying a method requires proving a large number of assertions.
Dafny uses a backend prover (an SMT solver) to verify assertions. The prover may become better or worse at verifying an assertion if you ask it to also verify another assertion. 
Dafny allows you to split up a group of assertions into batches, where each batch is sent to the SMT solver separately, so the verification of each batch is not influenced by the others.


One default way of operating is to combine all assertions into one batch, leading to a single run of the prover. 
 However, even when this is more efficient than the combination of proving each
assertion by itself (with prover start-up costs and the like for each one), it can also take quite a while to give a final result, possibly even timing-out.

So sometimes it is preferable to prove each assertion by itself, using the `-vcsSplitOnEveryAssert` command-line option.

But there are also intermediate options. Look at the various command-line options under "Verification-condition splitting".

Another way to split up the way in which assertions are grouped for proof is to use the two attributes `{:focus}` and `{:split_here}`,
both of which are applied to assert statements.

In brief, `{:focus}` says to focus on the block in which the attribute appears. Everything in that block is one assertion batch and everything
outside that block is another assertion batch. It does not matter where in the block the `{:focus}` attribute appears. If there are multiple
`{:focus}` attributes, each block containing one (or more) is one assertion batch, and everything outside of blocks containing `{:focus}` attributes
is a final assertion batch. This attibute is usually used to break out if-alternatives or loop-bodies into separate verification attempts.

`{:split_here}` creates an assertion batch of all assertions strictly before the attributed statement and another of the assertions at or after
the attributed statement. This attribute is usually used to break up long stretches of straight-line code.

Some examples that show how this works for multiple nested blocks are given in the reference manual, [here](../../DafnyRef/DafnyRef#sec-focus) and [here](../../DafnyRef/DafnyRef#sec-split_here).

# How does one declare a type to have a "default" initial value, say a type tagged with {:extern}?


## Question

How does one declare a type to have a "default" initial value, say a type tagged with {:extern}?

## Answer

There is no general way to do this. Subset types and newtypes have [witness](../DafnyRef/DafnyRef/#sec-witness-clauses) clauses and types that are [auto-initializable](../DafnyRef/DafnyRef#sec-auto-init)
have a default, but those rules do not apply to anonymous extern types.
Particularly for opaque types, there is not even a way to infer such a value.

You can manually initialize like this:
```dafny
type {:extern} TT {
}
function {:extern} init(): TT

method mmm() {
  var x: TT := init();
  var y:= x;
}
```


# A module A has names from an `import opened` of another module B, but if C imports A, it does not get those names. Please explain.


## Question

A module A has names from an `import opened` or another module B, but if C imports A, it does not get those names. Please explain.

## Answer

Here is some example code:
```dafny
module A {
  const a: int := 0
}

module B {
  import opened A
  const b: int := a; // This is A.a, known as a here because of the import opened
}

module C {
  import opened B
  const c: int := b; // This is B.b because of the import opened
  const d: int := A.a; // B.A is known as A because of the import opened in B
  const e: int := a; // ILLEGAL - opened is not transitive
}
```

The `import opened` directive brings into the importing module all the names declared in the imported module,
including the names of modules from import statements in the importee, but not names introduced into the importee (here `B`) by an import opened directive. `opened` is not transitive. As shown in the example code, the names in `A` are still available in `C` by qualifying them.

# Are there functional alternatives to recursive calls that are more efficient or use less stack space?


## Question

Are there functional alternatives to recursive calls that are more efficient or use less stack space?

## Answer

One way to reduce the number of recursive calls is to use Dafny's function-by-method construct to give a better performing implementation.
For example
```dafny
function Fib(n: nat): nat {
  if n < 2 then n else Fib(n-1) + Fib(n-2)
}
```
it a very natural but quite inefficient implementation of the Fibonacci function (it takes `Fib(n)` calls of `Fib` to compute `Fib(n)`, though only to a stack depth of `n`).

With function-by-method we can still use the natural recursive expression as the definition but provide a better performing implementation:
```dafny
function Fib(n: nat): nat
 {
  if n < 2 then n else Fib(n-1) + Fib(n-2)
} by method {
  var x := 0;
  var y := 1;
  for i := 0 to n 
    invariant x == Fib(i) && y == Fib(i+1)
  {
    x, y := y, x+y;
  }
  return x;
}
```
This implementation both combines the two computations of Fib and also, more importantly, turns a tail recursive recursion into a loop.

# How do I read a file as a string?


## Question

How do I read a file as a string? 

## Answer

You can't in pure Dafny. Not yet. Such a capability will eventually be part of a standard IO library.

What you can do is to write such a function in another language, say Java, and then use it in Dafny by extern declarations.

# Can I ask Dafny to not check termination of a function?


## Question

Can I ask dafny to not check termination of a function?

## Answer

Functions must always terminate, and it must be proved that they terminate.

Methods on the other hand should also terminate , but you can request the the proof be skipped using `decreases *`, as in
```dafny
method inf(i: int)
    decreases *
  {
      inf(i); 
  }
```

Eventually you should put an actual termination metric in place of the `*` and prove termination.
The reference manual has more information about termination metrics [in the section on `decreases` clauses](../DafnyRef/DafnyRef#sec-decreases-clause).

# What does {:termination false} do on trait? It looks like it is required if I want to extend traits from other modules.


## Question

What does `{:termination false}` do on trait? It looks like it is required if I want to extend traits from other modules.

## Answer

The attribute turns off termination checking for the trait. Here is an example
```dafny
module foo1 {

  trait {:termination false} Foo {
    method bar()
  }

  class Baz{

    static method boz(foo: Foo){ foo.bar(); }

  }
}
module foo2 {

  import opened foo1

  class Boz extends Foo {

    method bar(){
      Baz.boz(this);
    }
  }
}
```
In this example, omitting `{:termination false}` provokes the error "class 'Boz' is in a different module than trait 'foo1.Foo'. A class may only extend a trait in the same module, unless the parent trait is annotated with {:termination false}.".

The `{:termination false}` is only needed when there is dynamic dispatch across module boundaries.
It does put the onus on the user to prove termiation, as Dafny is no longer doing so.
The origin of this situation has to do with the interaction of current decreases clauses and traits.

Dafny decreases clauses were designed before the language had dynamic dispatch via trait members. As such, decreases clauses are made to be as simple as possible within each module, and decreases clauses are unnecessary across modules. When dynamic dispatch was added to the language, a draconian restriction was put in place to maintain soundness, namely to disallow dynamic dispatch across module boundaries. This is enforced by insisting that a class that implements a trait is declared in the same module that declares the trait.

The draconian restriction outlaws the useful case where a trait is placed in a library. Indeed, we are seeing this in [`dafny-lang/libraries`](https://github.com/dafny-lang/libraries/) now. So, Dafny supports a way for users to lift the draconian restriction and instead take responsibility themselves for termination of dynamically dispatched calls via a trait--it is to mark the trait with `{:termination false}`.

The status of solutions to this problem are discussed [here](https://github.com/dafny-lang/dafny/issues/1588).

# How do I make Dafny termination checking happy with mutual recursion?


## Question

How do I make Dafny termination checking happy with mutual recursion, like the following example:
```dafny
datatype T = Y | N | B(T,T)

function f(x : T) : bool {
    match x {
        case Y => true
        case N => false
        case B(x,y) => g(x,y)
    }
}

function g(x : T, y : T) : bool {
    f(x) && f(y)
}
```

If `g` is inlined there is no problem. What should I do?

## Answer

Termination of recursion is proved using a `decreases` clause. For the single function
Dafny can successfully guess a decreases metric. But for this mutual recursion case,
the user must supply on.

The termination metric for a recursive datatype (like `T` here) is the height of the tree denoted by the argument `x`, in this case.
So there is definitely a decrease in the metric from the call of `f` to the call of `g`, but there is not when `g` calls `f`.
One solution to this situation is the following:
```dafny
datatype T = Y | N | B(T,T)

function f(x : T) : bool 
  decreases x, 1
{
    match x {
        case Y => true
        case N => false
        case B(x,y) => g(x,y)
    }
}

function g(x : T, y : T) : bool 
  decreases B(x,y), 0
{
    f(x) && f(y)
}
```
Here when `f` calls `g`, the metric goes from `x, 1` to `B(x.x, x.y), 0`. Because `x` is the same as `B(x.x, x.y)`, the lexicographic ordering looks
at the next component, which does decrease from `1` to `0`. Then in each case that `g` calls `f`, the metric goes from `B(x,y), 0` to `x,1` or `y,1`,
which decreases on the first component.

Another solution, which is a pattern applicable in other circumstances as well, is to use a ghost parameter as follows:
```dafny
datatype T = Y | N | B(T,T)

function f(x : T) : bool
  decreases x, 1
{
  match x {
    case Y => true
    case N => false
    case B(x',y') => g(x,x',y')
  }
}

function g(ghost parent: T, x : T, y : T) : bool
  decreases parent, 0
  requires x < parent && y < parent
{
  f(x) && f(y)
}
```

More on the topic of termination metrics can be found [here](../DafnyRef/DafnyRef#sec-decreases-clause).

# Can it be proved that a class instance is not an instance of a trait?


## Question

Can it be proved that a class instance is not an instance of a trait, as in the following example?
```dafny
trait A<T> {}

class B {}

lemma Foo(v: object)
  ensures v is B ==> !(v is A<object>)
{}
```

## Answer

No. Although the lemma is valid and may be stated as an axiom, Dafny does not internally model
the type hierarchy and so does not have the information to prove that statement.
Such an axiom would have to be manually checked against the type hierarchy if the definitions of 
the types involved were to change.

# Is there a nice way to turn a `set` into a `seq`?


## Question

Is there a nice way to turn a set into a seq?

## Answer

There is as yet no built-in simple function but there are various idioms that can accomplish this task.

Within a method (where you can use a while loop), try `var acc: seq<int> := []; 
  while s != {} { var x: int :| x in s; acc := acc + [x]; s := s - {x}; }`

You could use a function-by-method to encapsulate the above in a function.

Here is an extended example taken from  [Dafny Power User: Iterating over a Collection](http://leino.science/papers/krml275.html).

```dafny
function SetToSequence<A(!new)>(s: set<A>, R: (A, A) -> bool): seq<A>
  requires IsTotalOrder(R)
  ensures var q := SetToSequence(s, R);
    forall i :: 0 <= i < |q| ==> q[i] in s
{
  if s == {} then [] else
    ThereIsAMinimum(s, R);
    var x :| x in s && forall y :: y in s ==> R(x, y);
    [x] + SetToSequence(s - {x}, R)
}

lemma ThereIsAMinimum<A(!new)>(s: set<A>, R: (A, A) -> bool)
  requires s != {} && IsTotalOrder(R)
  ensures exists x :: x in s && forall y :: y in s ==> R(x, y)
```

# How do I declare a default value for a parameter of a method or function?


## Question

How do I declare a default value for a parameter of a method or function?

## Answer

The parameters of methods and functions can be referred to by name.
```dafny
  method m( i: int,  j: int, k: int) {}
  method q() {
    m(4, k:= 7, j:=8);

  }
```
In the left-to-right sequence of actual arguments, once a parameter is referred to by name, all the rest must also be referred to by name. The named arguments may be in any order.

Furthermore, arguments can be given default values.
```dafny
  method m( i: int,  j: int, k: int := 0) {}
  method q() {
    m(4, 4, k:=8);
    m(1, j:=2);
    m(1,2);
  }
```
In the left-to-right sequence of actual arguments, once a parameter is given a default value, all the rest must also have a default value. Arguments may still be referred to by name, but now any named
argument with a default is optional. If there are no names at all, then it is always the last
arguments that are omitted if the actual argument list is shorter than the formal parameter list,
and they must all have defaults.

Finally, a parameter may be declared as `nameonly`, in which case it must be referred to by name.
```dafny
  method m( i: int,  j: int, nameonly k: int := 0, q: int := 8) {}
  method q() {
    // m(4, 4, 8 ); // Error
    m(4, 4, q:=9);
    m(4, 4, k:=8);
  }
```
Such a parameter may but does not need to have default value, but if it does not, it cannot be omitted.

# I just realized that a function I was compiling had a type error inside a match case.  Instead of giving a compile error I was getting a redundant clause warning for the second case. What is the reason for this?


## Question

I just realized that a function I was compiling had a type-error inside a match case.  Instead of giving a compile error I was getting a redundant clause warning for the second case. What is the reason for this?

## Answer

Here is a situation that can cause this error:
```dafny
datatype AB = A | B
method test(q: AB) {
  var c := match q { case a => true case b => false };
}
```
The example has an error on the second `case` saying this branch is redundant.

The problem here is that both `a` and `b` are undeclared variables. Consequently they both match
in match expression `q` no matter what `q`'s value is. Because `a` matches no matter what, 
the second case is redundant.

What is usually intended by such code is something like this:
```dafny
datatype AB = A | B
method test(q: AB) {
  var c := match q { case A => true case B => false };
}
```
which causes no type errors.

The observation here is that misspelled type names in case patterns can cause silent unexpected  behavior. It is likely that a lint warning will be produced for the above anti-pattern in some future version of Dafny.

# Is there a way I can pass a variable with a generic type to a method with a concrete type?


## Question

Is there a way I can pass a variable with a generic type to a method with a concrete type? Here is some motivating code:
```dafny
predicate Goo<K, V>(m: map<K, V>)
  requires m.keyType is string // Can I do something like this?
{ Foo(m) }

predicate Foo<V>(m: map<string, V>)
```

## Answer

In short, no.

There are a few problems here. First there is no way to extract the type of the keys of a map as a _type_ value. Dafny does not have the capability to reason about 
types as first-class entities. In fact the `is` operator takes a value and a type, not two types.

We could try writing the precondition as `requires m.Keys is set<string>`, but that is not permitted either as `m.Keys` is a `set<K>` and is not comparable to `set<string>` with `is`.
 

# How can ghost code call methods with side effects?


## Question

How can ghost code call methods with side effects?

## Answer

Ghost code may not have any effect on non-ghost state, but ghost code can have effects on ghost state.
So a ghost method may modify ghost fields, as long as the specifications list the appropriate fields in
the appropriate modifies clauses. The example code below demonstrates this:

```dafny
  class C {
    ghost var c: int

    ghost method m(k: int)
      modifies this
      ensures c == k
    { 
      c := k;
    }

    ghost method p() {
      var cc := new C;
      cc.m(8);
      assert cc.c == 8;
    }
  }
```

# How do I create and use an iterator?


## Question

How do I create and use an iterator?

## Answer

Here is an example of an iterator:
```dafny
iterator Gen(start: int) yields (x: int)
  yield ensures |xs| <= 10 && x == start + |xs| - 1
{
  var i := 0;
  while i < 10 invariant |xs| == i {
    x := start + i;
    yield;
    i := i + 1;
  }
}
```
An instance of this iterator is created using
```dafny
iter := new Gen(30);
```
It is used like this:
```
method Main() {
  var i := new Gen(30);
  while true
    invariant i.Valid() && fresh(i._new)
    decreases 10 - |i.xs|
  {
    var m := i.MoveNext();
    if (!m) {break; }
    print i.x;
  }
}
```
Here the method `MoveNext` and the field `xs` (and others) are automatically created, 
as decribed in the [reference manual](../DafnyRef/DafnyRef#sec-iterator-types).

Note that the syntax of iterators is under discussion in the Dafny development team and may change or have additional alternatives in the future.

# Can classes appear in specs?


## Question

Can classes appear in specs?

## Answer

Class types can be argument types for a method or function and the corresponding formal parameter can then be mentioned in specs.
Within the specs, you can call functions (ghost or not) of those classes.

However, there are some limitations:
- Primarily, the `new` operator may not be used in a specification, so new class objects cannot be allocated in the spec
- Note also that class objects are on the heap; as heap objects they will need to be mentioned in reads clauses.

# "How do I write specifications for a lambda expression in a sequence constructor?"


## Question

How do I write specifications for a lambda expression in a sequence constructor?

## Answer

Consider the code
```dafny
class C {
  var p: (int, int);
}

function Firsts0(cs: seq<C>): seq<int> {
  seq(|cs|, i => cs[i].p.0) // Two errors: `[i]` and `.p`
}
```

Dafny complains about the array index and an insufficient reads clause in the lambda function.
Both of these need specifications, but where are they to be written.

The specifications in a lamda function expression are written after the formal aarguments
but before the `=>`.

The array index problem is solved by a `requires` clause that limits the range of the index::
```dafny
class C {
  var p: (int, int);
}

function Firsts0(cs: seq<C>): seq<int> {
  seq(|cs|, i requires 0 <= i < |cs| => cs[i].p.0) // Two errors: `[i]` and `.p`
}
```

and the reads complaint by a `reads` clause that states which objects will be read.
In this case, it is the objects `cs[i]` that have their `p` field read.
If the element type of `cs` were a value type instead of a reference type, this
`reads` clause would be unnecessary.

```dafny
class C {
  var p: (int, int);
}

function Firsts2(cs: seq<C>): seq<int>
  reads set i | 0 <= i < |cs| :: cs[i]
{
  seq(|cs|, i
    requires 0 <= i < |cs|
    reads set i | 0 <= i < |cs| :: cs[i] => cs[i].p.0)
}
```

# Why can't I write 'forall t: Test :: t.i == 1' for an object t?


## Question:

Why can't I write `forall t: Test :: t.i == 1` for an object t?

## Answer:

This code

```dafny
trait Test {
 var i: int
}
class A {
  predicate testHelper() {
    forall t: Test :: t.i == 1
    // a forall expression involved in a predicate definition is not allowed to depend on the set of allocated references,
  }
}
```

can be better written as

```dafny
trait Test {
 var i: int
}
class A {
  ghost const allTests: set<Test>
  predicate testHelper() reads allTests {
    forall t: Test <- allTests :: t.i == 1
  }
}
```

That way, if you want to assume anything about the Test classes that you are modeling extern, 
you only need to specify an axiom that says that whatever Test you have was in allTests, 
which could have been a pool of Test objects created from the start anyway, and then you can use your axiom. 
# How do I say 'reads if x then this\`y else this\`z'? Dafny complains about the 'this'.


## Question: 

How do I say 'reads if x then this\`y else this\`z'? Dafny complains about the 'this'.

## Answer:

Here is some sample code that show a workaround.

```dafny
trait Test {
  var y: int
  var z: int
  function {:opaque} MyFunc(x: bool): int
    reads (if x then {this} else {})`y, (if x then {} else {this})`z {
    if x then y else z
  }
}

```
# How do I model extern methods that return objects?


## Question: 

How do I model extern methods that return objects?


## Answer:

When modeling extern functions that return objects, it's usually not good to have specifications that return objects. 
It's better to have a predicate that takes the input of a function, an object, and relates the two together.

For example:

```dafny
trait {:extern} {:compile false} Test {
  var i: int
  var y: int
}
trait {:extern} {:compile false} Importer {
  function Import(i: int): (r: Test)
    ensures r.i == i

  method {:extern} {:compile false} DoImport(i: int) returns (r: Test)
    ensures r == Import(i)

  predicate Conditions(i: int) {
     && var r := Import(i);
     && r.y == 2
  }
}
```

In this case, it's better to write a predicate, and use existential quantifiers along with the :| operator, 
and there no need to prove uniqueness because we are in ghost code!

```dafny
trait {:extern} {:compile false} Test {
  var i: int
}
trait {:extern} {:compile false} Importer {
  predicate IsImported(i: int, r: Test) {
    r.i == i
  }
  method {:extern} {:compile false} DoImport(i: int) returns (r: Test)
    ensures IsImported(i, r)

  predicate Conditions(i: int) {
     && (exists r: Test :: IsImported(i, r))
     && var r :| IsImported(i, r);   // Note the assignment has changed.
     && r.y == 2
  }
}
```
# Is there a Dafny style? and a Dafny linter (style checker and bad smell warnings)?


## Question

Is there a Dafny style? and a Dafny linter (style checker and bad smell warnings)?

## Answer

There is a Dafny style guide [here](https://dafny.org/dafny/StyleGuide/Style-Guide).

There is not yet a Dafny lint tool (that is, warnings about technically correct but suspicious or poor-style code),
though a formatter is underway. Warnings about some matters are included in the Dafny parser. 
However, ideas for lint warnings are being collected and you are welcome to contribute ideas: suggestions can be made on the [issues list](https://github.com/dafny-lang/dafny/issues).

# Is Dafny available as a library, to be called from other software?


## Question

Is Dafny available as a library, to be called from other software?

## Answer

Yes, it is. The DafnyPipeline library on NuGet is the most likely candidate for inclusion in a third-party program. 


# How do I run boogie manually?


## Question

How do I run Boogie manually? What Dafny output and command-line flags do I need?

## Answer

A Boogie file is generated by Dafny using the option `-print`. For example, the command `dafny -print:a.bpl HelloWorld.dfy` will produce a file `a.bpl`. 
If the `-print` option lacks an argument (the file name), the somewhat confusing message `Error: No input files were specified` is emitted.
Be cautious: `dafny -print A.dfy B.dfy` may overwrite `A.dfy`.
You can also use `-print:-` to send the boogie file to the standard output.

To run boogie, it is most convenient to install boogie directly. See https://github.com/boogie-org/boogie.
Dafny invokes Boogie as a library, not as a spawned executable, so there is no Boogie executable in the Dafny installation.
However, the version of Boogie that Dafny uses corresponds to Boogie 2.15.7 (as of Dafny 3.7.3). 


On a simple _Hello World_ program, `boogie a.bpl` is sufficient. Dafny does rely on these default Boogie options
- `smt.mbqi` is set `false`
- `model.compact` is set `false`
- `model.v2` is set `true`
- `pp.bv_literals` is set `false`

Dafny also sets these non-default Boogie options:
- `auto_config` is set `false`
- `type_check` is set `true`
- `smt.case_split` is set `3`
- `smt.qi.eager_threshold` is set `100`
- `smt.delay_units` is set `true`
- `smt.arith.solver` is set `2`

These all however are subject to change, especially as the version of Boogie used changes

In addition, Dafny sends a variety of other command-line options to Boogie, depending on selections by the user and heuristics built-in to Dafny.
Some guide to the available (Dafny) options that are passed through to Boogie are [in the reference manual](../../DafnyRef/DafnyRef#sec-controlling-boogie).

# Does Dafny verify methods in parallel?


## Question

Does Dafny verify methods in parallel?

## Answer

When used on the command-line, Dafny verifies each method in each module sequentially
and attempts to prove all the assertions in a method in one go.
However, you can use the option `/vcsCores` to parallelize some of the activity
and various options related to _verification condition splitting_ can break up the work
within a method.

When used in the IDE, the default is concurrent execution of proof attempts.


# Is there a doc generator for Dafny?


## Question

Is there a doc generator for Dafny?

## Answer

Not one produced by the Dafny team or included in a Dafny release.
This 3rd-party tool was reported by users: [https://github.com/nhweston/dfydoc](https://github.com/nhweston/dfydoc).


# How can I improve automation and performance for programs with non-linear arithmetic?


## Question

How can I improve automation and performance for programs with non-linear arithmetic?

## Answer

There are some switches (/arith and the somewhat deprecated /noNLarith) that reduce the automation you get with nonlinear arithmetic; they improve the overall proof success by using manually introduced lemmas instead. There are now also many lemmas about nonlinear arithmetic in the Dafny standard library.

# It looks like, when compiling to C#, my print statements don't show up if I don't have \n at the end of the string.


## Question

It looks like, when compiling to C#, my print statements don't show up if I don't have \n at the end of the string.

## Answer

The desired output is present in all current Dafny backends. But note that
if the print statement does not include the `\n`, then the output may not either.
In that case the output may be (depending on the shell you are using)
concatenated with the prompt for the next user input.

For example,
```dafny
method Main() {
  print "Hi";
}
```
produces (with a bash shell)
```
mydafny $ dafny run --target=cs Newline.dfy 

Dafny program verifier finished with 0 verified, 0 errors
Himydafny $
```

# Is there a standard library for Dafny?


## Question

Is there a standard library for Dafny?

## Answer

No, but one is planned. Some sample code is at [https://github.com/dafny-lang/libraries](https://github.com/dafny-lang/libraries). Contributions and ideas are welcome.

# Why do I need to use an old version of Z3?


## Question

Why do I need to keep using an old version of Z3?

## Answer

It is correct that the version of Z3 used by Dafny (through Boogie) is an old version.
Although the Dafny team would like to upgrade to newer versions of Z3 (to take advantage
of bug fixes, at a minimum), so far the newer versions of Z3 perform more poorly on
Dafny-generated SMT for many test cases.

# How do I ask a question or file a problem report or make a suggestion about Dafny?


## Question

How do I ask a question or file a problem report or make a suggestion about Dafny?

## Answer

You can ask questions about Dafny
- on Stack Overflow, tagged as 'dafny': [https://stackoverflow.com/questions/tagged/dafny](https://stackoverflow.com/questions/tagged/dafny)

You can report issues
- On the Dafny Issues log: [https://github.com/dafny-lang/dafny/issues](https://github.com/dafny-lang/dafny/issues)

Documentation about Dafny is available at [https://dafny.org](https://dafny.org) and links from there.

# Any plans to release the language server as a NuGet package? Seems like it’s not part of the Dafny release.


## Question

Any plans to release the language server as a NuGet package? Seems like it’s not part of the Dafny release.

## Answer

It is now available on NuGet, along with other components of the Dafny:
([https://www.nuget.org/packages?q=dafny](https://www.nuget.org/packages?q=dafny)):

# What compiler target langages are in development?


## Question

What compiler target langages are in development?

## Answer

As of version 3.7.3
- C#, Javascript, Java, and Go are well-supported
- Python is under development
- Limited support for C++ is available
- Rust support is being planned

# "Error: z3 cannot be opened because the developer cannot be verified"


This error occurs on a Mac after a new installation of Dafny, with Z3.
It is a result of security policies on the Mac.

You can fix the result by running the shell script `allow_on_mac.sh`
that is part of the release.

The problem can arise with other components of Dafny as well.


# "Error: rbrace expected"


The error "rbrace expected"
is a common occurence caused by some parsing error within a brace-enclosed block, such as a module declaration, a class declaration, or a block statement.
The error means that the parser does not expect whatever characters it next sees. Consequently, the parser just says that it expects the block to be closed by a right curly brace (`}`).
Indeed, one cause might be an inadvertently omitted right brace.

Here are some other examples:

- A misspelled keyword introducing the next declaration
```
{% include_relative ERROR_Rbrace4.dfy %}
```
- A `const` initializer follows ':=', not '='
```
{% include_relative ERROR_Rbrace1.dfy %}
```
- A field (`var`) does not take an initializer
```
{% include_relative ERROR_Rbrace3.dfy %}
```
- A field (`var`) does not take an initializer, and if it did it would follow a `:=`, not a `=`
```
{% include_relative ERROR_Rbrace2.dfy %}
```

# "Error: closeparen expected"


## Question

What causes the error "Error: closeparen expected" as in

```dafny
{% include_relative ERROR_CloseParen.dfy %}
```
producing
```text
{% include_relative ERROR_CloseParen.txt %}
```

## Answer

You are writing a Java/C parameter declaration. In Dafny, parameter declarations have the form `name: type`, so
```dafny
method test(i: int) { ... }
```

# "Error: cannot establish the existence of LHS values that satisfy the such-that predicate"


Here is example code that produces this error:
```dafny
{% include_relative ERROR_NoLHS.dfy %}
```


When a _such-that_ (`:|`) initialization is used, Dafny must be able to establish that there is at least one value
that satisfies the predicate given on the RHS. 
That is, in this case, it must prove
`assert exists k :: k in m;`.
But for this example, if the map `m` is empty, there is no such value,
so the error message results.

If you add a precondition that the map is non-empty, then the error is gone:
```
{% include_relative ERROR_NoLHS1.dfy %}
```

# "Error: type parameter 0 (K) passed to type A must support no references"


Ordinarily, a type parameter `X` can be instantiated with any type.

However, in some cases, it is desirable to say that `X` is only allowed to be instantiated by types that have certain characteristics. One such characteristic is that the type does not have any references.

A “reference”, here, refers to a type that is or contains a reference type. Reference types are class and trait types. So, if a type parameter is restricted to only “no reference” types, then you cannot instantiate it with a class type or a trait type.
A datatype can also include a reference. For example,
datatype MyDatatype = Ctor(x: MyClass)
More subtly, a type
datatype D<X> = Ctor(x: X)
might also contain a reference type if `X` is a type that can contain a reference type.


If you’re getting the “no reference” error, then you’re either trying to write an unbounded quantifier over a type that may contain references, or you’re trying to use a type that may contain references to instantiate a type parameter restricted to no-reference types.
Type characteristics that a type parameter must satisfy are written in parentheses after the type name and are separated by commas. For example, to say that a type parameter `X` must not contain any references, you would declare it as `X(!new)`. To further ensure it supports compile-time equality, you would declare it as `X(!new,==)`.
Presumably, you’re trying to instantiate a type parameter like `X(!new)` with a type that may contain references.

There is more discussion of type parameter characteristics in the [reference manual](../../DafnyRef/DafnyRef#sec-type-parameters).

# "Error: a modifies-clause expression must denote an object or a set/iset/multiset/seq of objects (instead got map<int, A>)"



Here is example code that produces the given error message:
```dafny
{% include_relative ERROR_ModifiesValue.dfy %}
```

The expression in the modifies clause is expected to be a set of object references.
It is permitted also to be a comma-separated list of object references or sets or sequences of such references.
In this example, the expression is none of these; instead it is a `map`.
`map`s are values and so are not modified; new values are created, just like an integer is not modified  one computes a different integer value.

If the intent here is to say that any of the `A` objects stored in the map may be modified, then one has to construct a set of all those objects.
For a map, there is an easy way to do this: just say `m.Values`, as in this rewrite of the example:
```
{% include_relative ERROR_ModifiesValue1.dfy %}
```

# "Error: name of datatype (String) is used as a function?"


How do I fix this error message: "name of datatype (String) is used as a function"?

```dafny
module MString {
  export provides String
  datatype String = String(s: string)
}
module MX {
  import opened MString
  const S := String("asd")
}
```

The names visible in module `MX` are the datatype `String` but not its constructor, since 
the dataype is only imported as `provides`.
Consequently, the only option for the name `String` in module `MX` is that datatype, 
which then causes the error message.

The fix to this is to declare the export as `export reveals String`.
If `String` is meant to be opaque (only provided) then you cannot construct elements of it; 
if it is meant to be transparent, then you must reveal it.

# "Error: possible violation of function precondition for op(v)"


Here is code that provoked this error (though the error message as been made more specific in later releases):
```dafny
ghost function Eval(): string -> bool {
   EvalOperator(Dummy)
}

ghost function EvalOperator(op: string -> bool): string -> bool 
{
  (v: string) => op(v)
}

function Dummy(str: string): bool
  requires str == []
```

The problem has to do with [arrow types](../../DafnyRef/DafnyRef#sec-arrow-types).
In particular here, the argument of `EvalOperator` takes a `->` function, which is a total, heap-independent function.
However, its argument, `Dummy`, is a partial, heap-independent function, because it has a precondition.
If you want `EvalOperator` to be flexible enough to take partial functions, then declare `op` to have the type
`string --> bool`.

There is more on arrow types in the [reference manual](../DafnyRef/DafnyRef.html#sec-arrow-subset-types);

# "Error: type ? does not have a member IsFailure"


The `IsFailure` member is a necessary part of [_failure-compatible_ types](../..//DafnyRef/DafnyRef#sec-failure-compatible-types), which are used with the `:-` operator.
See the discussion in the reference manual for more detail.

# "Error: value does not satisfy subset constraints of T"


The error "value does not satisfy subset constraints of T"
for some type name `T` arises when a value is trying to be converted to a subset type `T`,
and the value cannot be proved to satisfy the predicate that defines the subset type.

This is pretty clear when one is trying to assign, say an `int` to a `nat`, but is more complex when using generic types.

This example
```dafny
{% include_relative ERROR_Covariance.dfy %}
```
produces
```text
{% include_relative ERROR_Covariance.txt %}
```

The problem is that the code is trying to convert a `formula<neg>` to a `formula<real>`.
While a `neg` is a subtype of `real`, that does not imply a subtype relationship between
`formula<neg>` and `formula<real>`.
That relationship must be declared in the definition of `formula`.
By default, the definition of a generic type is _non-variant_, meaning there is no
subtype relationship between `formula<T>` and `formula<U>` when `T` is a subtype of `U`.
What is wanted here is for `formula` to be _covariant_, so that
`formula<T>` is a subtype of `formula<U>` when `T` is a subtype of `U`.
For that, use the declaration `formula<+T>`.

To declare `formula` as _contravariant_ use `formula<-T>`. Then `formula<U>` is a subtype of `formula<T>` when `T` is a subtype of `U`.

Type parameter characteristics are discussed in [the reference manual](../DafnyRef/DafnyRef.html#sec-type-parameter-variance)

# "Error: function precondition might not hold"


This error can occur when trying to write a sequence comprehension expression like
```dafny
{% include_relative ERROR_SeqComp.dfy %}
```
which produces
```text
{% include_relative ERROR_SeqComp.txt %}
```

The problem is that current Dafny does not implicitly impose the condition that the function used to initialize the 
sequence elements is only called with `nat` values less than the size of the new sequence. That condition has to be made explicit:
```dafny
{% include_relative ERROR_SeqComp1.dfy %}
```

# "Error: insufficient reads clause to invoke function"


Example: This code
```
{% include_relative ERROR_InsufficientReads.dfy %}
```
produces this output:
```
{% include_relative ERROR_InsufficientReads.txt %}
```

This error message indicates that a nested call of a function needs a bigger `reads` set than its enclosing function provides.

Another situation provoking this error is this:
```dafny
class A {
  var x: int
  predicate IsSpecial() reads this {
    x == 2
  }
}
type Ap  = x : A | x.IsSpecial() witness *
```
In this case the error message is a bit misleading. The real problem is that the predicate in the subset declaration (that is, `x.IsSpecial()`)
is not allowed to depend on the heap, as `IsSpecial` does. If such a dependency were allowed, then changing some values in the heap could
possibly change the predicate such that a value which was allowed in the subset type now suddenly is not. This situation would be a disaster for both
soundness and ease of reasoning.

Another variation on the above is this example:
```dafny
trait A { var x: int }
type AZero = a: A | a.x == 0 witness *
```
where again the predicate depends on a heap variable `x`, which Dafny does not permit.

And a final example:
```dafny
datatype Foo = Foo | Foofoo

class Bar {
  var foo: set<Foo>;
  function method getFoo(): set<Foo> { this.foo }
}
```
which produces `Error: insufficient reads clause to read field`. In this case the function `getFoo` does indeed have an insufficient reads clause, as
it does not have one, yet it reads a field of `this`. You can insert either `reads this` or ``reads this`foo`` before the left brace.

The code in the original question is fixed like this:
```
{% include_relative ERROR_InsufficientReads1.dfy %}
```

# Cannot export mutable field 'x' without revealing its enclosing class 'A'


An example of this error is the code
```dafny
{% include_relative ERROR_MutableField.dfy %}
```
which produces the error
```text
{% include_relative ERROR_MutableField.txt %}
```

By only providing `A`, importers will know that `A` is a type, 
but won’t know that it is a reference type (here, a class). 
This makes it illegal to refer to a mutable field such as in the reads clause. 
So, you have to export A by revealing it.

Note, `export reveals A` does not export the members of A 
(except, it does export the anonymous constructor of A, if there is one). 
So, you still have control over which members of A to export.

The following code verifies without error:
```dafny
{% include_relative ERROR_MutableField1.dfy %}
```



# "Error: this symbol not expected in Dafny"


This error message is not clear and may come from a variety of sources. Here is one:
```dafny
{% include_relative ERROR_PostconditionLemma.dfy %}
```
which produces 
```text
{% include_relative ERROR_PostconditionLemma.txt %}
```

The error message points to the token `true` as the unexpected symbol.
`true` is definitely a legitimate symbol in Dafny.

The problem is that the `;` in the `ensures` clause is seen as the (optional) semicolon that can end
the clause. Thus the `true` is interpreted as the (illegal) start to a new clause (or a `{` to start the body).

The correct way to include a lemma with the postcondition is to use parentheses:
`ensures (L(); true)

# "Prover error: Unexpected prover response (getting info about 'unknown' response): (:reason-unknown 'Overflow encountered when expanding old_vector')"


This error is caused by a bug in the Z3 backend tool used by Dafny. 
As of v3.9.0 there is work underway to update Z3 to a more recent version.
Until then, the best you can do is to try to change the verification condition sent to Z3 by splitting it up, using various Dafny options and attributes like `{:split_here}`, `{:focus}`, `/vcsSplitOnEveryAssert`, `/vcsMaxSplits`, and `/randomSeed`.


# "Warning: file contains no code"


This warning can occur if a file being compiled by Dafny is completely empty.
Previous other occurences of this warning were bugs.


# "Duplicate name of import: ..."


This error results from importing two modules with the same name. For example
```dafny
import A.Util
import B.util
```
In this case, the default name given to the two imports is the same: `Util`.
To give them different names, use the longer form of the import statement
```dafny
import A.Util
import BU = B.Util;
```
Now a name `N` from `A.Util` can  be referred to as `Util.N` and
a name `N` from `B.Util` can be referred to as `BU.N`.

# "Warning: /!\ No terms found to trigger on."


This warning occurred with the following code:
```dafny
predicate ExistsSingleInstance(s : string32, delim : string32)
  {
    exists pos : nat ::
      (pos <= |s| - |delim| && forall x : nat :: x < |delim| ==> s[pos + x] == delim[x]) &&
      forall pos' : nat :: (pos' <= |s| - |delim| && forall y : nat :: y < |delim| ==> s[pos' + y] == delim[y]) ==> pos == pos'
  }
```

The verifier uses quantifications by finding good ways to instantiate them.
More precisely, it uses `forall` quantifiers by instantiating them and it proves `exists` quantifiers by finding witnesses for them.
The warning you’re getting says that nothing stands out to the verifier as a good way to figure out good instantiations.

In the case of `pos`, this stems from the fact that a good instantiation would be some `pos` for which the verifier already knows either `pos <= …` or `forall x :: …`, the former of which is not specific enough and the latter is too complicated for it to consider.

The “no trigger” warning is fixed by this refactoring:
```dafny
predicate SingleInstance(s: string, delim: string, pos: nat)
{
  pos <= |s| - |delim| &&
  forall x : nat :: x < |delim| ==> s[pos + x] == delim[x]
}

predicate ExistsSingleInstance'(s: string, delim: string)
{
  exists pos : nat ::
    SingleInstance(s, delim, pos) &&
    forall pos' : nat :: SingleInstance(s, delim, pos') ==> pos == pos'
}
```

One more remark: The “no trigger” warning should be taken seriously, because it’s usually a sign that there will be problems with using the formula and/or problems with verification performance.

# "Error: value does not satisfy the subset constraints of '(seq<uint8>, Materials.EncryptedDataKey) -> seq<uint8>' (possible cause: it may be partial or have read effects)"


Here is an example of submitted code that produced this error:
```dafny
function EncryptedDataKeys(edks: Msg.EncryptedDataKeys):  (ret: seq<uint8>)
  requires edks.Valid()
{
    UInt16ToSeq(|edks.entries| as uint16) + FoldLeft(FoldEncryptedDataKey, [], edks.entries)
}

function FoldEncryptedDataKey(acc: seq<uint8>, edk: Materials.EncryptedDataKey): (ret: seq<uint8>)
  requires edk.Valid()
{
    acc + edk.providerID + edk.providerInfo + edk.ciphertext
}
```

The general cause of this error is supplying some value to a situation where (a) the type of the target (declared variable, formal argument) is a subset type and (b) Dafny cannot prove that the value falls within the predicate for the subset type. In this example code, `uint8` is likely a subset type and could be at fault here.
But more likely and less obvious is supplying `FoldEncryptedDataKey` as the actual argument to `FoldLeft`.

The signature of `FoldLeft` is `function {:opaque} FoldLeft<A,T>(f: (A, T) -> A, init: A, s: seq<T>): A`.
Note that the type of the function uses a `->` arrow, namely a total, heap-independent function (no requires or reads clause).
But `FoldEncryptedDataKey` does have a requires clause. Since `->` functions are a subset type of partial, heap-dependent `~>` functions,
the error message complains about the subset type constraints not being satisfied.

These various arrow types are described in the [release notes](https://github.com/dafny-lang/dafny/releases/tag/v2.0.0)
when they were first added to the language. They are also documented in the [reference manual](../DafnyRef/DafnyRef#sec-arrow-types).
