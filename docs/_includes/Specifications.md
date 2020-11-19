# Specifications
Specifications describe logical properties of Dafny methods, functions,
lambdas, iterators and loops. They specify preconditions, postconditions,
invariants, what memory locations may be read or modified, and
termination information by means of _specification clauses_.
For each kind of specification, zero or more specification
clauses (of the type accepted for that type of specification)
may be given, in any order.

We document specifications at these levels:

- At the lowest level are the various kinds of specification clauses,
  e.g., a ``RequiresClause_``.
- Next are the specifications for entities that need them,
  e.g., a ``MethodSpec``.
- At the top level are the entity declarations that include
  the specifications, e.g., ``MethodDecl``.

This section documents the first two of these in a bottom-up manner.
We first document the clauses and then the specifications
that use them.

## Specification Clauses

### Requires Clause

````grammar
RequiresClause_ =
  "requires" Expression(allowLemma: false, allowLambda: false)
````

The `requires` clauses specify preconditions for methods,
functions, lambda expressions and iterators. Dafny checks
that the preconditions are met at all call sites. The
callee may then assume the preconditions hold on entry.

If no `requires` clause is specified it is taken to be `true`.

If more than one `requires` clause is given, then the
precondition is the conjunction of all of the expressions
from all of the `requires` clauses. The order of conjunctions
(and hence the order of `requires` clauses with respect to each other)
can be important: earlier conjuncts can set conditions that
establish that later conjuncts are well-defined.

### Ensures Clause

````grammar
EnsuresClause_ =
  "ensures" { Attribute } Expression(allowLemma: false,
                                     allowLambda: false)

ForAllEnsuresClause_ =
  "ensures" Expression(allowLemma: false, allowLambda: true)

FunctionEnsuresClause_ =
  "ensures" Expression(allowLemma: false, allowLambda: false)
````

An `ensures` clause specifies the post condition for a
method, function or iterator.

If no `ensures` clause is specified it is taken to be `true`.

If more than one `ensures` clause is given, then the
postcondition is the conjunction of all of the expressions
from all of the `ensures` clauses.
The order of conjunctions
(and hence the order of `ensures` clauses with respect to each other)
can be important: earlier conjuncts can set conditions that
establish that later conjuncts are well-defined.

TODO: In the present sources ``FunctionEnsuresClause_`` differs from
``EnsuresClause_`` only in that it is not allowed to specify
``Attribute``s. This seems like a bug and will likely
be fixed in a future version.

### Decreases Clause
````grammar
DecreasesClause_(allowWildcard, allowLambda) =
  "decreases" { Attribute } DecreasesList(allowWildcard,
                                          allowLambda)

FunctionDecreasesClause_(allowWildcard, allowLambda) =
  "decreases" DecreasesList(allowWildcard, allowLambda)

DecreasesList(allowWildcard, allowLambda) =
  PossiblyWildExpression(allowLambda)
  { "," PossiblyWildExpression(allowLambda) }
````
If `allowWildcard` is false but one of the
``PossiblyWildExpression``s is a wild-card, an error is
reported.

TODO: A ``FunctionDecreasesClause_`` is not allowed to specify
``Attribute``s. this will be fixed in a future version.

Decreases clauses are used to prove termination in the
presence of recursion. if more than one `decreases` clause is given
it is as if a single `decreases` clause had been given with the
collected list of arguments. That is,

```dafny
decreases A, B
decreases C, D
```

is equivalent to

```dafny
decreases A, B, C, D
```
Note that changing the order of multiple `decreases` clauses will change
the order of the expressions within the equivalent single `decreases`
clause, and will therefore have different semantics.

If any of the expressions in the `decreases` clause are wild (i.e., `*`)
then the proof of termination will be skipped.

Termination metrics in Dafny, which are declared by `decreases` clauses,
are lexicographic tuples of expressions. At each recursive (or mutually
recursive) call to a function or method, Dafny checks that the effective
`decreases` clause of the callee is strictly smaller than the effective
`decreases` clause of the caller.

 What does "strictly smaller" mean? Dafny provides a built-in
 well-founded order for every type and, in some cases, between types. For
 example, the Boolean "false" is strictly smaller than "true", the
 integer 78 is strictly smaller than 102, the set `{2,5}` is strictly
 smaller than the set `{2,3,5}`, and for "s" of type `seq<Color>` where
 `Color` is some inductive datatype, the color `s[0]` is strictly less than
 `s` (provided `s` is nonempty).

What does "effective decreases clause" mean? Dafny always appends a
"top" element to the lexicographic tuple given by the user. This top
element cannot be syntactically denoted in a Dafny program and it never
occurs as a run-time value either. Rather, it is a fictitious value,
which here we will denote $\top$, such that each value that can ever occur
in a Dafny program is strictly less than $\top$. Dafny sometimes also
prepends expressions to the lexicographic tuple given by the user. The
effective decreases clause is any such prefix, followed by the
user-provided decreases clause, followed by $\top$. We said "user-provided
decreases clause", but if the user completely omits a `decreases` clause,
then Dafny will usually make a guess at one, in which case the effective
decreases clause is any prefix followed by the guess followed by $\top$.
(If you're using the Dafny IDE in Visual Studio, you can hover the mouse
over the name of a recursive function or method, or the "while" keyword
for a loop, to see the `decreases` clause that Dafny guessed, if any.)

Here is a simple but interesting example: the Fibonacci function.

```dafny
function Fib(n: nat) : nat
{
  if n < 2 then n else Fib(n-2) + Fib(n-1)
}

```

In this example, if you hover your mouse over the function name
you will see that Dafny has supplied a `decreases n` clause.

Let's take a look at the kind of example where a mysterious-looking
decreases clause like "Rank, 0" is useful.

Consider two mutually recursive methods, `A` and `B`:
```dafny
method A(x: nat)
{
  B(x);
}

method B(x: nat)
{
  if x != 0 { A(x-1); }
}
```

To prove termination of `A` and `B`, Dafny needs to have effective
decreases clauses for A and B such that:

* the measure for the callee `B(x)` is strictly smaller than the measure
  for the caller `A(x)`, and

* the measure for the callee `A(x-1)` is strictly smaller than the measure
  for the caller `B(x)`.

Satisfying the second of these conditions is easy, but what about the
first? Note, for example, that declaring both `A` and `B` with "decreases x"
does not work, because that won't prove a strict decrease for the call
from `A(x)` to `B(x)`.

Here's one possibility (for brevity, we will omit the method bodies):
```dafny
method A(x: nat)
  decreases x, 1

method B(x: nat)
  decreases x, 0
```

For the call from `A(x)` to `B(x)`, the lexicographic tuple `"x, 0"` is
strictly smaller than `"x, 1"`, and for the call from `B(x)` to `A(x-1)`, the
lexicographic tuple `"x-1, 1"` is strictly smaller than `"x, 0"`.

 Two things to note: First, the choice of "0" and "1" as the second
 components of these lexicographic tuples is rather arbitrary. It could
 just as well have been "false" and "true", respectively, or the sets
 `{2,5}` and `{2,3,5}`. Second, the keyword `decreases` often gives rise to
 an intuitive English reading of the declaration. For example, you might
 say that the recursive calls in the definition of the familiar Fibonacci
 function `Fib(n)` "decreases n". But when the lexicographic tuple contains
 constants, the English reading of the declaration becomes mysterious and
 may give rise to questions like "how can you decrease the constant 0?".
 The keyword is just that---a keyword. It says "here comes a list of
 expressions that make up the lexicographic tuple we want to use for the
 termination measure". What is important is that one effective decreases
 clause is compared against another one, and it certainly makes sense to
 compare something to a constant (and to compare one constant to
 another).

 We can simplify things a little bit by remembering that Dafny appends
 $\top$ to the user-supplied decreases clause. For the A-and-B example,
 this lets us drop the constant from the `decreases` clause of A:

```dafny
method A(x: nat)
   decreases x

method B(x: nat)
  decreases x, 0
```

The effective decreases clause of `A` is $(x, \top)$ and the effective
decreases clause of `B` is $(x, 0, \top)$. These tuples still satisfy the two
conditions $(x, 0, \top) < (x, \top)$ and $(x-1, \top) < (x, 0, \top)$. And
as before, the constant "0" is arbitrary; anything less than $\top$ (which
is any Dafny expression) would work.

Let's take a look at one more example that better illustrates the utility
of $\top$. Consider again two mutually recursive methods, call them `Outer`
and `Inner`, representing the recursive counterparts of what iteratively
might be two nested loops:
```dafny
method Outer(x: nat)
{
  // set y to an arbitrary non-negative integer
  var y :| 0 <= y;
  Inner(x, y);
}

method Inner(x: nat, y: nat)
{
  if y != 0 {
    Inner(x, y-1);
  } else if x != 0 {
    Outer(x-1);
  }
}
```
The body of `Outer` uses an assign-such-that statement to represent some
computation that takes place before `Inner` is called. It sets "y" to some
arbitrary non-negative value. In a more concrete example, `Inner` would do
some work for each "y" and then continue as `Outer` on the next smaller
"x".

Using a `decreases` clause $(x, y)$ for `Inner` seems natural, but if
we don't have any bound on the size of the $y$ computed by `Outer`,
there is no expression we can write in the `decreases` clause of `Outer`
that is sure to lead to a strictly smaller value for $y$ when `Inner`
is called. $\top$ to the rescue. If we arrange for the effective
decreases clause of `Outer` to be $(x, \top)$ and the effective decreases
clause for `Inner` to be $(x, y, \top)$, then we can show the strict
decreases as required. Since $\top$ is implicitly appended, the two
decreases clauses declared in the program text can be:
```dafny
method Outer(x: nat)
  decreases x

method Inner(x: nat, y: nat)
  decreases x, y
```
Moreover, remember that if a function or method has no user-declared
`decreases` clause, Dafny will make a guess. The guess is (usually)
the list of arguments of the function/method, in the order given. This is
exactly the decreases clauses needed here. Thus, Dafny successfully
verifies the program without any explicit decreases clauses:
```dafny
method Outer(x: nat)
{
  var y :| 0 <= y;
  Inner(x, y);
}

method Inner(x: nat, y: nat)
{
  if y != 0 {
    Inner(x, y-1);
  } else if x != 0 {
    Outer(x-1);
  }
}
```
The ingredients are simple, but the end result may seem like magic. For many users, however, there may be no magic at all -- the end result may be so natural that the user never even has to be bothered to think about that there was a need to prove termination in the first place.


### Framing
````grammar
FrameExpression(allowLemma, allowLambda) =
  ( Expression(allowLemma, allowLambda) [ FrameField ]
  | FrameField )

FrameField = "`" Ident

PossiblyWildFrameExpression(allowLemma) =
  ( "*" | FrameExpression(allowLemma, allowLambda: false) )
````

Frame expressions are used to denote the set of memory locations
that a Dafny program element may read or write. A frame
expression is a set expression. The form `{}` (that is, the empty set)
says that no memory locations may be modified,
which is also the default if no `modifies` clause is given explicitly.

Note that framing only applies to the heap, or memory accessed through
references. Local variables are not stored on the heap, so they cannot be
mentioned (well, they are not in scope in the declaration) in reads
annotations. Note also that types like sets, sequences, and multisets are
value types, and are treated like integers or local variables. Arrays and
objects are reference types, and they are stored on the heap (though as
always there is a subtle distinction between the reference itself and the
value it points to.)

The ``FrameField`` construct is used to specify a field of a
class object. The identifier following the back-quote is the
name of the field being referenced.
If the `FrameField` is preceded by an expression the expression
must be a reference to an object having that field.
If the `FrameField` is not preceded by an expression then
the frame expression is referring to that field of the current
object. This form is only used within a method of a class or trait.

The use of ``FrameField`` is discouraged as in practice it has not
been shown to either be more concise or to perform better.
Also, there's (unfortunately) no form of it for array
elements---one could imagine

```dafny
  modifies a`[j]
```
Also, ``FrameField`` is not taken into consideration for
lambda expressions.

### Reads Clause
````grammar
FunctionReadsClause_ =
  "reads"
  PossiblyWildFrameExpression (allowLemma: false)
  { "," PossiblyWildFrameExpression(allowLemma: false) }

LambdaReadsClause_ =
  "reads" PossiblyWildFrameExpression(allowLemma: true)
  { "," PossiblyWildFrameExpression(allowLemma: true) }

IteratorReadsClause_ =
  "reads" { Attribute }
  FrameExpression(allowLemma: false, allowLambda: false)
  { "," FrameExpression(allowLemma: false, allowLambda: false) }

PossiblyWildExpression(allowLambda) =
  ( "*" | Expression(allowLemma: false, allowLambda) )
````

Functions are not allowed to have side effects; they may also be restricted in
what they can read. The _reading frame_ of a function (or predicate) is all
the memory locations that the function is allowed to read. The reason we
might limit what a function can read is so that when we write to memory,
we can be sure that functions that did not read that part of memory have
the same value they did before. For example, we might have two arrays,
one of which we know is sorted. If we did not put a reads annotation on
the sorted predicate, then when we modify the unsorted array, we cannot
determine whether the other array stopped being sorted. While we might be
able to give invariants to preserve it in this case, it gets even more
complex when manipulating data structures. In this case, framing is
essential to making the verification process feasible.

It is not just the body of a function that is subject to `reads`
checks, but also its precondition and the `reads` clause itself.

A reads clause can list a wildcard `*`, which allows the enclosing
function to read anything. In many cases, and in particular in all cases
where the function is defined recursively, this makes it next to
impossible to make any use of the function. Nevertheless, as an
experimental feature, the language allows it (and it is sound).
Note that a `*` makes the rest of the frame expression irrelevant.

A `reads` clause specifies the set of memory locations that a function,
lambda, or iterator may read. If more than one `reads` clause is given
in a specification the effective read set is the union of the sets
specified. If there are no `reads` clauses the effective read set is
empty. If `*` is given in a `reads` clause it means any memory may be
read.

TODO: It would be nice if the different forms of read clauses could be
combined. In a future version the single form of read clause will allow
a list and attributes.

TO BE WRITTEN: multiset of objects allowed in reads clauses

### Modifies Clause

````grammar
ModifiesClause_ =
  "modifies" { Attribute }
  FrameExpression(allowLemma: false, allowLambda: false)
  { "," FrameExpression(allowLemma: false, allowLambda: false) }
````

Frames also affect methods. Methods are not
required to list the things they read. Methods are allowed to read
whatever memory they like, but they are required to list which parts of
memory they modify, with a `modifies` annotation. These are almost identical
to their reads cousins, except they say what can be changed, rather than
what the value of the function depends on. In combination with reads,
modification restrictions allow Dafny to prove properties of code that
would otherwise be very difficult or impossible. Reads and modifies are
one of the tools that allow Dafny to work on one method at a time,
because they restrict what would otherwise be arbitrary modifications of
memory to something that Dafny can reason about.

If an object is newly allocated within the body of a method
or within the scope of a modifies statement or a loop's modifies clause,
 then the fields of that object may always be modified.

It is also possible to frame what can be modified by a block statement
by means of the block form of the
[modify statement](#sec-modify-statement) (Section [#sec-modify-statement]).

A `modifies` clause specifies the set of memory locations that a
method, iterator or loop body may modify. If more than one `modifies`
clause is given in a specification, the effective modifies set is the
union of the sets specified. If no `modifies` clause is given the
effective modifies set is empty. A loop can also have a
`modifies` clause. If none is given, the loop may modify anything
the enclosing context is allowed to modify.

Note that _modifies_ here is used in the sense of _writes_. That is, a field
that may not be modified may not be written to, even with the same value it
already has or even if the value is restored later. The terminology and
semantics varies among specification languages. Some define frame conditions
in this sense (a) of _writes_ and others in the sense (b) that allows writing
a field with the same value or changing the value so long as the original
value is restored by the end of the scope. For example, JML defines
`assignable` and `modifies` as synonyms in the sense (a), though KeY
interprets JML's `assigns/modifies` in sense (b).
ACSL and ACSL++ use the `assigns` keyword, but with _modify_ (b) semantics.
Ada/SPARK's dataflow contracts encode _write_ (a) semantics.

### Invariant Clause
````grammar
InvariantClause_ =
  "invariant" { Attribute }
  Expression(allowLemma: false, allowLambda: true)
````

An `invariant` clause is used to specify an invariant
for a loop. If more than one `invariant` clause is given for
a loop the effective invariant is the conjunction of
the conditions specified.

The invariant must hold on entry to the loop. And assuming it
is valid on entry, Dafny must be able to prove that it then
holds at the end of the loop.

## Method Specification
````grammar
MethodSpec =
  { ModifiesClause_
  | RequiresClause_
  | EnsuresClause_
  | DecreasesClause_(allowWildcard: true, allowLambda: false)
  }
````

A method specification is zero or more `modifies` `requires`
`ensures` or `decreases` clauses, in any order.
A method does not have `reads` clauses because methods are allowed to
read any memory.

## Function Specification
````grammar
FunctionSpec =
  { RequiresClause_
  | FunctionReadsClause_
  | FunctionEnsuresClause_
  | FunctionDecreasesClause_(allowWildcard: false, allowLambda: false)
  }
````

A function specification is zero or more `reads` `requires`
`ensures` or `decreases` clauses, in any order. A function
specification does not have `modifies` clauses because functions are not
allowed to modify any memory.

## Lambda Specification
````grammar
LambdaSpec_ =
  { LambdaReadsClause_
  | RequiresClause_
  }
````

A lambda specification is zero or more `reads` or `requires` clauses.
Lambda specifications do not have `ensures` clauses because the body
is never opaque.
Lambda specifications do not have `decreases`
clauses because they do not have names and thus cannot be recursive. A
lambda specification does not have `modifies` clauses because lambdas
are not allowed to modify any memory.

## Iterator Specification
````grammar
IteratorSpec =
  { IteratorReadsClause_
  | ModifiesClause_
  | [ "yield" ] RequiresClause_
  | [ "yield" ] EnsuresClause_
  | DecreasesClause_(allowWildcard: false, allowLambda: false)
  }
````

An iterator specification applies both to the iterator's constructor
method and to its `MoveNext` method. The `reads` and `modifies`
clauses apply to both of them. For the `requires` and `ensures`
clauses, if `yield` is not present they apply to the constructor,
but if `yield` is present they apply to the `MoveNext` method.

TODO: What is the meaning of a `decreases` clause on an iterator?
Does it apply to `MoveNext`? Make sure our description of
iterators explains these.

TODO: What is the relationship between the post condition and
the `Valid()` predicate?

## Loop Specification
````grammar
LoopSpec =
  { InvariantClause_
  | DecreasesClause_(allowWildcard: true, allowLambda: true)
  | ModifiesClause_
  }
````

A loop specification provides the information Dafny needs to
prove properties of a loop. The ``InvariantClause_`` clause
is effectively a precondition and it along with the
negation of the loop test condition provides the postcondition.
The ``DecreasesClause_`` clause is used to prove termination.

## Auto-generated boilerplate specifications

TO BE WRITTEN - {:autocontracts}
