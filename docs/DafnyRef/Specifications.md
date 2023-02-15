# 7. Specifications {#sec-specifications}

Specifications describe logical properties of Dafny methods, functions,
lambdas, iterators and loops. They specify preconditions, postconditions,
invariants, what memory locations may be read or modified, and
termination information by means of _specification clauses_.
For each kind of specification, zero or more specification
clauses (of the type accepted for that type of specification)
may be given, in any order.

We document specifications at these levels:

- At the lowest level are the various kinds of specification clauses,
  e.g., a ``RequiresClause``.
- Next are the specifications for entities that need them,
  e.g., a ``MethodSpec``, which typically consist of a sequence of
  specification clauses.
- At the top level are the entity declarations that include
  the specifications, e.g., ``MethodDecl``.

This section documents the first two of these in a bottom-up manner.
We first document the clauses and then the specifications
that use them.

Specification clauses typically appear in a sequence. They all begin with a 
keyword and do not end with semicolons.

## 7.1. Specification Clauses {#sec-specification-clauses}


Within expressions in specification clauses, you can use
[specification expressions](#sec-list-of-specification-expressions) along with any [other expressions](#sec-expressions) you need.

### 7.1.1. Requires Clause ([grammar](#g-requires-clause)) {#sec-requires-clause}

Examples:
<!-- %check-resolve -->
```dafny
method m(i: int)
  requires true
  requires i > 0
  requires L: 0 < i < 10
```

The `requires` clauses specify preconditions for methods,
functions, lambda expressions and iterators. Dafny checks
that the preconditions are met at all call sites. The
callee may then assume the preconditions hold on entry.

If no `requires` clause is specified, then a default implicit
clause `requires true` is used.

If more than one `requires` clause is given, then the
precondition is the conjunction of all of the expressions
from all of the `requires` clauses, with a collected list
of all the given Attributes. The order of conjunctions
(and hence the order of `requires` clauses with respect to each other)
can be important: earlier conjuncts can set conditions that
establish that later conjuncts are well-defined.

The attributes recognized for requires clauses are discussed in [Section 11.3](#sec-verification-attributes-on-assertions).

### 7.1.2. Ensures Clause ([grammar](#g-ensures-clause)) {#sec-ensures-clause}

Examples:
<!-- %check-resolve -->
```dafny
method m(i: int) returns (r: int)
  ensures r > 0
```

An `ensures` clause specifies the post condition for a
method, function or iterator.

If no `ensures` clause is specified, then a default implicit
clause `ensures true` is used.

If more than one `ensures` clause is given, then the
postcondition is the conjunction of all of the expressions
from all of the `ensures` clauses, with a
collected list of all the given Attributes.
The order of conjunctions
(and hence the order of `ensures` clauses with respect to each other)
can be important: earlier conjuncts can set conditions that
establish that later conjuncts are well-defined.

The attributes recognized for ensures clauses are discussed in [Section 11.3](#sec-verification-attributes-on-assertions).

### 7.1.3. Decreases Clause ([grammar](#g-decreases-clause)) {#sec-decreases-clause}

Examples:
<!-- %check-resolve -->
```dafny
method m(i: int, j: int) returns (r: int)
  decreases i, j
method n(i: int) returns (r: int)
  decreases *
```
Decreases clauses are used to prove termination in the
presence of recursion. If more than one `decreases` clause is given
it is as if a single `decreases` clause had been given with the
collected list of arguments and a collected list of Attributes. That is,

<!-- %no-check -->
```dafny
decreases A, B
decreases C, D
```

is equivalent to

<!-- %no-check -->
```dafny
decreases A, B, C, D
```
Note that changing the order of multiple `decreases` clauses will change
the order of the expressions within the equivalent single `decreases`
clause, and will therefore have different semantics.

Loops and compiled methods (but not functions and not ghost methods,
including lemmas) can be specified to be possibly non-terminating.
This is done by declaring the method or loop with `decreases *`, which
causes the proof of termination to be skipped. If a `*` is present
in a `decreases` clause, no other expressions are allowed in the
`decreases` clause. A method that contains a possibly non-terminating
loop or a call to a possibly non-terminating method must itself be
declared as possibly non-terminating.

Termination metrics in Dafny, which are declared by `decreases` clauses,
are lexicographic tuples of expressions. At each recursive (or mutually
recursive) call to a function or method, Dafny checks that the effective
`decreases` clause of the callee is strictly smaller than the effective
`decreases` clause of the caller.

 What does "strictly smaller" mean? Dafny provides a built-in
 well-founded order for every type and, in some cases, between types. For
 example, the Boolean `false` is strictly smaller than `true`, the
 integer `78` is strictly smaller than `102`, the set `{2,5}` is strictly
 smaller than (because it is a proper subset of) the set `{2,3,5}`, and for `s` of type `seq<Color>` where
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

Here is a simple but interesting example: the Fibonacci function.

<!-- %check-verify -->
```dafny
function Fib(n: nat) : nat
{
  if n < 2 then n else Fib(n-2) + Fib(n-1)
}
```

In this example, Dafny supplies a `decreases n` clause.

Let's take a look at the kind of example where a mysterious-looking
decreases clause like "Rank, 0" is useful.

Consider two mutually recursive methods, `A` and `B`:
<!-- %check-verify Specifications.1.expect -->
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

Here's one possibility:
<!-- %check-verify -->
```dafny
method A(x: nat)
  decreases x, 1
{
  B(x);
}

method B(x: nat)
  decreases x, 0
{
  if x != 0 { A(x-1); }
}
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

<!-- %check-verify -->
```dafny
method A(x: nat)
   decreases x
{
  B(x);
}

method B(x: nat)
  decreases x, 0
{
  if x != 0 { A(x-1); }
}
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
<!-- %check-verify -->
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
<!-- %check-verify -->
```dafny
method Outer(x: nat)
  decreases x
{
  // set y to an arbitrary non-negative integer
  var y :| 0 <= y;
  Inner(x, y);
}

method Inner(x: nat, y: nat)
  decreases x,y
{
  if y != 0 {
    Inner(x, y-1);
  } else if x != 0 {
    Outer(x-1);
  }
}
```
Moreover, remember that if a function or method has no user-declared
`decreases` clause, Dafny will make a guess. The guess is (usually)
the list of arguments of the function/method, in the order given. This is
exactly the decreases clauses needed here. Thus, Dafny successfully
verifies the program without any explicit `decreases` clauses:
<!-- %check-verify -->
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
The ingredients are simple, but the end result may seem like magic. 
For many users, however, there may be no magic at all 
-- the end result may be so natural that the user never even has to 
be bothered to think about that there was a need to prove 
termination in the first place.

Dafny also prepends two expressions to the user-specified (or guessed) tuple of expressions
in the decreases clause. The first expression is the ordering of
the module containing the decreases clause in the dependence-ordering of 
modules. That is, a module that neither imports or defines (as submodules) any other modules 
has the lowest value in the order and every other module has a value that is higher than
that of any module it defines or imports. As a module cannot call a method in a
module that it does not depend on, this is an effective first component to the
overall decreases tuple.

The second prepended expression represents the position
of the method in the call graph within a module. Dafny analyzes the call-graph of the 
module, grouping all methods into mutually-recursive groups.
Any method that calls nothing else is at the lowest level (say level 0).
Absent recursion, every method has a level value strictly greater than any method it calls.
Methods that are mutually recursive are at the same level and they are above
the level of anything else they call. With this level value prepended to 
the decreases clause, the decreases tuple automatically decreases on any
calls in a non-recursive context.

Though Dafny fixes a well-founded order that it uses when checking
termination, Dafny does not surface this ordering directly in
expressions. That is, syntactically, there is no single operator that
stands for the well-founded ordering.

### 7.1.4. Framing ([grammar](#g-frame-expression)) {#sec-frame-expression}

Examples:
<!-- %no-check -->
```dafny
*
o
o`a
`a
{ o, p, q }
{}
```

Frame expressions are used to denote the set of memory locations
that a Dafny program element may read or write. 
They are used in `reaqds` and `modifies` clauses.
A frame expression is a set expression. The form `{}` is the empty set.
The type of the frame expression is `set<object>`.

Note that framing only applies to the heap, or memory accessed through
references. Local variables are not stored on the heap, so they cannot be
mentioned (well, they are not in scope in the declaration) in frame
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
object (`this`). This form is only used within a method of a class or trait.

A ``FrameField`` can be useful in the following case:
When a method modifies only one field, rather than writing

<!-- %check-verify -->
```dafny
class A {
  var i: int
  var x0: int
  var x1: int
  var x2: int
  var x3: int
  var x4: int
  method M()
    modifies this
    ensures unchanged(`x0) && unchanged(`x1) && unchanged(`x2) && unchanged(`x3) && unchanged(`x4)
  { i := i + 1; }
}
```

one can write the more concise:

<!-- %check-verify -->
```dafny
class A {
  var i: int
  var x0: int
  var x1: int
  var x2: int
  var x3: int
  var x4: int
  method M()
    modifies `i
  { i := i + 1; }
}
```

There's (unfortunately) no form of it for array
elements -- but to account for unchanged elements, you can always write
`forall i | 0 <= i < |a| :: unchanged(a[i])`.

A ``FrameField`` is not taken into consideration for
lambda expressions.

### 7.1.5. Reads Clause ([grammar](#g-reads-clause)) {#sec-reads-clause}

Examples:
<!-- %no-check -->
```dafny
const o: object
const o, oo: object
function f()
  reads *
function g()
  reads o, oo
function h()
  reads { o }
```

Functions are not allowed to have side effects; they may also be restricted in
what they can read. The _reading frame_ of a function (or predicate) consists of all
the heap memory locations that the function is allowed to read. The reason we
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

A `reads` clause can list a wildcard `*`, which allows the enclosing
function to read anything. In many cases, and in particular in all cases
where the function is defined recursively, this makes it next to
impossible to make any use of the function. Nevertheless, as an
experimental feature, the language allows it (and it is sound).
If a `reads` clause uses `*`, then the `reads` clause is not allowed to
mention anything else (since anything else would be irrelevant, anyhow).

A `reads` clause specifies the set of memory locations that a function,
lambda, or iterator may read. The readable memory locations are all the fields
of all of the references given in the set specified in the frame expression
and the single fields given in [`FrameField`](#sec-frame-expression) elements of the frame expression.
For example, in
<!-- %check-verify -->
```dafny
class C {
  var x: int
  var y: int

  predicate f(c: C) 
    reads this, c`x
  {
    this.x == c.x
  }
}
```
the `reads` clause allows reading `this.x`, `this,y`, and `c.x` (which may be the same
memory location as `this.x`).
}

If more than one `reads` clause is given
in a specification the effective read set is the union of the sets
specified. If there are no `reads` clauses the effective read set is
empty. If `*` is given in a `reads` clause it means any memory may be
read.

If a `reads` clause refers to a sequence or multiset, that collection
(call it `c`) is converted to a set by adding an implicit set
comprehension of the form `set o: object | o in c` before computing the
union of object sets from other `reads` clauses.

An expression in a `reads` clause is also allowed to be a function call whose value is 
a collection of references. Such an expression is converted to a set by taking the
union of the function's image over all inputs. For example, if `F` is
a function from `int` to `set<object>`, then `reads F` has the meaning

<!-- %no-check -->
```dafny
set x: int, o: object | o in F(x) :: o
```

For each function value `f`, Dafny defines the function `f.reads`,
which takes the same arguments as `f` and returns that set of objects
that `f` reads (according to its reads clause) with those arguments.
`f.reads` has type `T ~> set<object>`, where `T` is the input type(s) of `f`.

This is particularly useful when wanting to specify the reads set of
another function. For example, function `Sum` adds up the values of
`f(i)` where `i` ranges from `lo` to `hi`:

<!-- %check-verify -->
```dafny
function Sum(f: int ~> real, lo: int, hi: int): real
  requires lo <= hi
  requires forall i :: lo <= i < hi ==> f.requires(i)
  reads f.reads
  decreases hi - lo
{
  if lo == hi then 0.0 else
    f(lo) + Sum(f, lo + 1, hi)
}
```

Its `reads` specification says that `Sum(f, lo, hi)` may read anything
that `f` may read on any input.  (The specification
`reads f.reads` gives an overapproximation of what `Sum` will actually
read. More precise would be to specify that `Sum` reads only what `f`
reads on the values from `lo` to `hi`, but the larger set denoted by
`reads f.reads` is easier to write down and is often good enough.)

Note, only `reads` clauses, not `modifies` clauses, are allowed to
include functions as just described.

### 7.1.6. Modifies Clause ([grammar](#g-modifies-clause)) {#sec-modifies-clause}

Examples:
<!-- %check-resolve -->
```dafny
class A { var f: int }
const o: object?
const p: A?
method M()
  modifies { o, p }
method N()
  modifies { }
method Q()
  modifies o, p`f
```

Frames also affect methods. Methods are not
required to list the things they read. Methods are allowed to read
whatever memory they like, but they are required to list which parts of
memory they modify, with a `modifies` annotation. These are almost identical
to their `reads` cousins, except they say what can be changed, rather than
what the value of the function depends on. In combination with reads,
modification restrictions allow Dafny to prove properties of code that
would otherwise be very difficult or impossible. Reads and modifies are
one of the tools that allow Dafny to work on one method at a time,
because they restrict what would otherwise be arbitrary modifications of
memory to something that Dafny can reason about.

Just as for a `reads` clause, the memory locations allowed to be modified
in a method are all the fields of any object reference in the frame expression
set and any specific field denoted by a [`FrameField`](#sec-frame-expression) in the `modifies` clause.
For example, in
<!-- %check-resolve -->
```dafny
class C {
  var next: C?
  var value: int

  method M() 
    modifies next
  { 
    ... 
  }
}
```
method `M` is permitted to modify `this.next.next` and `this.next.value`
but not `this.next`. To be allowed to modify `this.next`, the modifies clause
must include `this`, or some expression that evaluates to `this`, or ``this`next``.

If an object is newly allocated within the body of a method
or within the scope of a `modifies` statement or a loop's `modifies` clause,
 then the fields of that object may always be modified.

A `modifies` clause specifies the set of memory locations that a
method, iterator or loop body may modify. If more than one `modifies`
clause is given in a specification, the effective modifies set is the
union of the sets specified. If no `modifies` clause is given the
effective modifies set is empty. There is no wildcard (`*`) allowed in
a modifies clause. A loop can also have a
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

### 7.1.7. Invariant Clause ([grammar](#g-invariant-clause)) {#sec-invariant-clause}

Examples:
<!-- %check-resolve-warn Specifications.2.expect -->
```dafny
method m()
{
  var i := 10;
  while 0 < i
    invariant 0 <= i < 10
}
```

An `invariant` clause is used to specify an invariant
for a loop. If more than one `invariant` clause is given for
a loop, the effective invariant is the conjunction of
the conditions specified, in the order given in the source text.

The invariant must hold on entry to the loop. And assuming it
is valid on entry to a particular iteration of the loop, 
Dafny must be able to prove that it then
holds at the end of that iteration of the loop.

## 7.2. Method Specification ([grammar](#g-method-specification)) {#sec-method-specification}

Examples:
<!-- %check-resolve -->
```dafny
class C {
  var next: C?
  var value: int

  method M(i: int) returns (r: int)
    requires i >= 0
    modifies next
    decreases i
    ensures r >= 0
  { 
    ... 
  }
}
```

A method specification consists of zero or more `modifies`, `requires`,
`ensures` or `decreases` clauses, in any order.
A method does not have `reads` clauses because methods are allowed to
read any memory.

## 7.3. Function Specification ([grammar](#g-function-specification)) {#sec-function-specification}

Examples:
<!-- %check-resolve -->
```dafny
class C {
  var next: C?
  var value: int

  function M(i: int): (r: int)
    requires i >= 0
    reads this
    decreases i
    ensures r >= 0
  { 
    0 
  }
}
```

A function specification is zero or more `reads`, `requires`,
`ensures` or `decreases` clauses, in any order. A function
specification does not have `modifies` clauses because functions are not
allowed to modify any memory.

## 7.4. Lambda Specification ([grammar](#g-lambda-specification)) {#sec-lambda-specification}

A lambda specification provides a specification for a lambda function expression;
it consists of zero or more `reads` or `requires` clauses.
Any `requires` clauses may not have labels or attributes.
Lambda specifications do not have `ensures` clauses because the body
is never opaque.
Lambda specifications do not have `decreases`
clauses because lambda expressions do not have names and thus cannot be recursive. A
lambda specification does not have `modifies` clauses because lambdas
are not allowed to modify any memory.

## 7.5. Iterator Specification ([grammar](#g-iterator-specification)) {#sec-iterator-specification}

An iterator specification may contains `reads`, `modifies`, 
`decreases`, `requires`, `yield requires, `ensures`
and `yield ensures` clauses.

An iterator specification applies both to the iterator's constructor
method and to its `MoveNext` method.
- The `reads` and `modifies`
clauses apply to both of them. 
- The `requires` and `ensures` clauses apply to the constructor.
- The `yield requires` and `yield ensures` clauses apply to the `MoveNext` method.

Examples of iterators, including iterator specifications, are given in
[Section 5.11](#sec-iterator-types). Briefly
- a requires clause gives a precondition for creating an iterator
- an ensures clause gives a postcondition when the iterator exits (after all iterations are complete)
- a decreases clause is used to show that the iterator will eventually terminate
- a yield requires clause is a precondition for calling `MoveNext`
- a yield ensures clause is a postcondition for calling `MoveNext`

## 7.6. Loop Specification ([grammar](#g-loop-specification)) {#sec-loop-specification}

A loop specification provides the information Dafny needs to
prove properties of a loop. It contains `invariant`,
`decreases`, and `modifies` clauses.

The `invariant` clause
is effectively a precondition and it along with the
negation of the loop test condition provides the postcondition.
The `decreases` clause is used to prove termination.

## 7.7. Auto-generated boilerplate specifications

AutoContracts is an experimental feature that inserts much of the dynamic-frames boilerplate
into a class. The user simply
- marks the class with `{:autocontracts}` and
- declares a function (or predicate) called Valid().

AutoContracts then

- Declares, unless there already exist members with these names:
<!-- %no-check -->
```dafny
  ghost var Repr: set(object)
  predicate Valid()
```

- For function/predicate `Valid()`, inserts
<!-- %no-check -->
```dafny
  reads this, Repr
  ensures Valid() ==> this in Repr
```
- Into body of `Valid()`, inserts (at the beginning of the body)
<!-- %no-check -->
```dafny
  this in Repr && null !in Repr
```
  and also inserts, for every array-valued field `A` declared in the class:
<!-- %no-check -->
```dafny
  (A != null ==> A in Repr) &&
```
  and for every field `F` of a class type `T` where `T` has a field called `Repr`, also inserts
<!-- %no-check -->
```dafny
  (F != null ==> F in Repr && F.Repr SUBSET Repr && this !in Repr && F.Valid())
```
  except, if `A` or `F` is declared with `{:autocontracts false}`, then the implication will not
be added.
- For every constructor, inserts
<!-- %no-check -->
```dafny
  ensures Valid() && fresh(Repr)
```
- At the end of the body of the constructor, adds
<!-- %no-check -->
```dafny
   Repr := {this};
   if (A != null) { Repr := Repr + {A}; }
   if (F != null) { Repr := Repr + {F} + F.Repr; }
```

In all the following cases, no `modifies` clause or `reads` clause is added if the user
has given one.

- For every non-static non-ghost method that is not a "simple query method",
inserts
<!-- %no-check -->
```dafny
   requires Valid()
   modifies Repr
   ensures Valid() && fresh(Repr - old(Repr))
```
- At the end of the body of the method, inserts
<!-- %no-check -->
```dafny
   if (A != null && !(A in Repr)) { Repr := Repr + {A}; }
   if (F != null && !(F in Repr && F.Repr SUBSET Repr)) { Repr := Repr + {F} + F.Repr; }
```
- For every non-static non-twostate method that is either ghost or is a "simple query method",
add:
<!-- %no-check -->
```dafny
   requires Valid()
```
- For every non-static twostate method, inserts
<!-- %no-check -->
```dafny
   requires old(Valid())
```
- For every non-"Valid" non-static function, inserts
<!-- %no-check -->
```dafny
   requires Valid()
   reads Repr
```
