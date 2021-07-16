# 20. Expressions
The grammar of Dafny expressions follows a hierarchy that
reflects the precedence of Dafny operators. The following
table shows the Dafny operators and their precedence
in order of increasing binding power.

 operator                 | description
--------------------------|------------------------------------
 `;`                      | That is [LemmaCall; Expression](#sec-top-level-expression)
--------------------------|------------------------------------
 `<==>`                   | [equivalence (if and only if)](#sec-equivalence)
--------------------------|------------------------------------
 `==>`                    | [implication (implies)](#sec-implication)
 `<==`                    | reverse implication (follows from)
--------------------------|------------------------------------
 `&&`, `&`                | conjunction (and)
 `||`, `|`                | disjunction (or)
--------------------------|------------------------------------
 `==`                     | equality
 `==#[k]`                 | prefix equality (co-inductive)
 `!=`                     | disequality
 `!=#[k]`                 | prefix disequality (co-inductive)
 `<`                      | less than
 `<=`                     | at most
 `>=`                     | at least
 `>`                      | greater than
 `in`                     | collection membership
 `!in`                    | collection non-membership
 `!!`                     | disjointness
--------------------------|------------------------------------
 `<<`                     | left-shift
 `>>`                     | right-shift
--------------------------|------------------------------------
 `+`                      | addition (plus)
 `-`                      | subtraction (minus)
--------------------------|------------------------------------
 `*`                      | multiplication (times)
 `/`                      | division (divided by)
 `%`                      | modulus (mod)
--------------------------|------------------------------------
 `|`                      | bit-wise or
 `&`                      | bit-wise and
 `^`                      | bit-wise exclusive-or (not equal)
--------------------------|------------------------------------
 `as` operation           | [type conversion](#sec-as-expression)
 `is` operation           | [type conversion](#sec-as-expression)
--------------------------|------------------------------------
 `-`                      | arithmetic negation (unary minus)
 `!`                      | logical negation, bit-wise complement
--------------------------|------------------------------------
 Primary Expressions      |

We are calling the ``UnaryExpression``s that are neither
arithmetic nor logical negation the _primary expressions_.
They are the most tightly bound.

In the grammar entries below we explain the meaning when the
operator for that precedence level is present. If the
operator is not present then we just descend to the
next precedence level.

## 20.1. Top-level expressions {#sec-top-level-expression}
````grammar
Expression(allowLemma, allowLambda) =
    EquivExpression(allowLemma, allowLambda)
    [ ";" Expression(allowLemma, allowLambda) ]
````

The "allowLemma" argument says whether or not the expression
to be parsed is allowed to have the form `S;E` where `S` is a call to a lemma.
"allowLemma" should be passed in as "false" whenever the expression to
be parsed sits in a context that itself is terminated by a semi-colon.

The "allowLambda" says whether or not the expression to be parsed is
allowed to be a lambda expression.  More precisely, an identifier or
parenthesized-enclosed comma-delimited list of identifiers is allowed to
continue as a lambda expression (that is, continue with a `reads`, `requires`,
or `=>`) only if "allowLambda" is true.  This affects function/method/iterator
specifications, if/while statements with guarded alternatives, and expressions
in the specification of a lambda expression itself.

Sometimes an expression will fail unless some relevant fact is known.
In the following example the `F_Fails` function fails to verify
because the `Fact(n)` divisor may be zero. But preceding
the expression by a lemma that ensures that the denominator
is not zero allows function `F_Succeeds` to succeed.
```dafny
function Fact(n: nat): nat
{
  if n == 0 then 1 else n * Fact(n-1)
}

lemma L(n: nat)
  ensures 1 <= Fact(n)
{
}

function F_Fails(n: nat): int
{
  50 / Fact(n)  // error: possible division by zero
}

function F_Succeeds(n: nat): int
{
  L(n); // note, this is a lemma call in an expression
  50 / Fact(n)
}
```

## 20.2. Equivalence Expressions {#sec-equivalence}
````grammar
EquivExpression(allowLemma, allowLambda) =
  ImpliesExpliesExpression(allowLemma, allowLambda)
  { "<==>" ImpliesExpliesExpression(allowLemma, allowLambda) }
````
An ``EquivExpression`` that contains one or more "<==>"s is
a boolean expression and all the contained ``ImpliesExpliesExpression``
must also be boolean expressions. In that case each "<==>"
operator tests for logical equality which is the same as
ordinary equality.

See [Section 0](#sec-equivalence-operator] for an explanation of the
`<==>` operator as compared with the `==` operator.

## 20.3. Implies or Explies Expressions {#sec-implication}
````grammar
ImpliesExpliesExpression(allowLemma, allowLambda) =
  LogicalExpression(allowLemma, allowLambda)
  [ (  "==>" ImpliesExpression(allowLemma, allowLambda)
    | "<==" LogicalExpression(allowLemma, allowLambda)
            { "<==" LogicalExpression(allowLemma, allowLambda) }
    )
  ]

ImpliesExpression(allowLemma, allowLambda) =
  LogicalExpression(allowLemma, allowLambda)
  [  "==>" ImpliesExpression(allowLemma, allowLambda) ]
````

See [Section 7.1.3](#sec-implication-and-reverse-implication)] for an explanation
of the `==>` and `<==` operators.

## 20.4. Logical Expressions

````grammar
LogicalExpression(allowLemma, allowLambda) =
  RelationalExpression(allowLemma, allowLambda)
  [ ( "&&" RelationalExpression(allowLemma, allowLambda)
           { "&&" RelationalExpression(allowLemma, allowLambda) }
    | "||" RelationalExpression(allowLemma, allowLambda)
           { "||" RelationalExpression(allowLemma, allowLambda) }
    )
  ]
  | { "&&" RelationalExpression(allowLemma, allowLambda) }
  | { "||" RelationalExpression(allowLemma, allowLambda) }
````

Note that the Dafny grammar allows a conjunction or disjunction to be
_prefixed_ with `&&` or `||` respectively. This form simply allows a
parallel structure to be written:
```dafny
var b: bool :=
  && x != null
  && y != null
  && z != null
  ;
```
This is purely a syntactic convenience allowing easy edits such as reordering
lines or commenting out lines without having to check that the infix
operators are always where they should be.

See [Section 7.1.2](#sec-conjunction-and-disjunction) for an explanation
of the `&&` and `||` operators.

## 20.5. Relational Expressions
````grammar
RelationalExpression(allowLemma, allowLambda) =
  ShiftTerm(allowLemma, allowLambda)
  { RelOp ShiftTerm(allowLemma, allowLambda) }

RelOp =
  ( "=="
    [ "#" "[" Expression(allowLemma: true, allowLambda: true) "]" ]
  | "!="
    [ "#" "[" Expression(allowLemma: true, allowLambda: true) "]" ]
  | "<" | ">" | "<=" | ">="
  | "in"
  | "!in"
  | "!!"
  )

````

The relation expressions that have a ``RelOp`` compare two or more terms.
As explained in section [#sec-basic-types], `==`, `!=`, ``<``, `>`, `<=`, and `>=`
are _chaining_.

The `in` and `!in` operators apply to collection types as explained in
[Section 10](#sec-collection-types) and represent membership or non-membership
respectively.

The `!!` represents disjointness for sets and multisets as explained in
[Section 10.1](#sec-sets) and [Section 10.2](#sec-multisets).

Note that `x ==#[k] y` is the prefix equality operator that compares
co-inductive values for equality to a nesting level of k, as
explained in section [#sec-co-equality].

## 20.6. Bit Shifts
````grammar
ShiftTerm(allowLemma, allowLambda) =
  Term(allowLemma, allowLambda)
  { ShiftOp Term(allowLemma, allowLambda) }

ShiftOp = ( "<<" | ">>" )
````

These operators are the left and right shift operators for bit-vector values.
They take a bit-vector value and an `int`, shifting the bits by the given
amount; the result has the same bit-vector type as the LHS.
For the expression to be well-defined, the RHS value must be in the range 0 to the number of
bits in the bit-vector type, inclusive.

The operations are left-associative: `a << i >> j` is `(a << i) >> j`.
## 20.7. Terms
````grammar
Term(allowLemma, allowLambda) =
  Factor(allowLemma, allowLambda)
  { AddOp Factor(allowLemma, allowLambda) }

AddOp = ( "+" | "-" )
````

`Terms` combine `Factors` by adding or subtracting.
Addition has these meanings for different types:

* Arithmetic addition for numeric types ([Section 7.2](#sec-numeric-types)]).
* Union for sets and multisets ([Section 10.1](#sec-sets) and [Section 10.2](#sec-multisets))
* Concatenation for sequences ([Section 10.3](#sec-sequences))
* Map merging for maps ([Section 10.4](#sec-maps)).

Subtraction is arithmetic subtraction for numeric types, and set or multiset
subtraction for sets and multisets, and domain subtraction for maps.

## 20.8. Factors
````grammar
Factor(allowLemma, allowLambda) =
  BitvectorFactor(allowLemma, allowLambda)
  { MulOp BitvectorFactor(allowLemma, allowLambda) }

MulOp = ( "*" | "/" | "%" )
````

A ``Factor`` combines ``UnaryExpression``s using multiplication,
division, or modulus. For numeric types these are explained in
[Section 7.2](#sec-numeric-types).
As explained there, `/` and `%` on `int` values represent _Euclidean_
integer division and modulus and not the typical C-like programming
language operations.

Only `*` has a non-numeric application. It represents set or multiset
intersection as explained in [Section 10.1](#sec-sets) and [Section 10.2](#sec-multisets).

## 20.9. Bit-vector Operations
````grammar
BitvectorFactor(allowLemma, allowLambda) =
  AsExpression(allowLemma, allowLambda)
  { BVOp AsExpression(allowLemma, allowLambda) }

BVOp = ( "|" | "&" | "^" )
````

These operations take two bit-vector values of the same type, returning
a value of the same type. The operations perform bit-wise _or_ (`|`),
_and_ (`&`), and _exclusive-or_ (`^`). To perform bit-wise equality, use
`^` and `!` (unary complement) together.

These operations associate to the left but do not associate with each other;
use parentheses: `a & b | c` is illegal; use `(a & b) | c` or `a & (b | c)`
instead.

Bit-vector operations are not allowed in some contexts.
The `|` symbol is used both for bit-wise or and as the delimiter in a
[cardinality](#sec-cardinality-expression) expression: an ambiguity arise if
the expression E in `| E |` contains a `|`. This situation is easily
remedied; just enclose E in parentheses, as in `|(E)|`.
The only type-correct way this can happen is if the expression is
a comprehension, as in `| set x: int :: x | 0x101 |`.

## 20.10. As (Conversion) and Is (type test) Expressions {#sec-as-expression}
````grammar
AsExpression(allowLemma, allowLambda) =
  UnaryExpression(allowLemma, allowLambda)
  { ( "as" | "is" ) Type }
````
The `as` expression converts the given `UnaryExpression` to the stated
`Type`, with the result being of the given type. The following combinations
of conversions are permitted:

* Any type to itself
* Any int or real based numeric type or bit-vector type to another int or real based numeric type or bit-vector type
* Any base type to a subset or newtype with that base
* Any subset or newtype or to its base type or a subset or newtype of the same base
* Any type to a subset of newtype that has the type as its base
* Any trait to a class or trait that extends that trait
* Any class or trait to a trait extended by that class or trait

Some of the conversions above are already implicitly allowed, without the
`as` operation, such as from a subset type to its base. In any case, it
must be able to be proved that the value of the given expression is a
legal value of the given type. For example, `5 as MyType` is permited (by the verifier) only if `5` is a legitimate value of`MyType` (which must be a numeric type).

The `as` operation is like a grammatical suffix or postfix operation.
However, note that the unary operations bind more tightly than does `as`.
That is `- 5 as nat` is `(- 5) as nat` (which fails), whereas `a * b as nat`
is `a * (b as nat)`. On the other hand, `- a[4]` is `- (a[4])`.

The `is` expression is grammatically similar to the `as` expression, with the
same binding power. The `is` expression is a run-time type test that
returns a `bool` value indicating whether the LHS expression is a legal
value of the RHS type. The expression can be used to check
whether a trait value is of a particular class type. That is, the expression
in effect checks the allocated type of a trait.

The RHS type of an `is` expression can always be a supertype of the type of the LHS
expression. Other than that, the RHS must be based on a reference type and the
LHS expression must be assignable to the RHS type. Furthermore, in order to be
compilable, the RHS type must not be a subset type other than a non-null reference
type, and the type parameters of the RHS must be uniquely determined from the
type parameters of the LHS type. The last restriction is designed to make it
possible to perform type tests without inspecting type parameters at run time.
For example, consider the following types:

```dafny
trait A { }
trait B<X> { }
class C<Y> extends B<Y> { }
class D<Y> extends B<set<Y>> { }
class E extends B<int> { }
class F<Z> extends A { }
```

A LHS expression of type `B<set<int>>` can be used in a type test where the RHS is
`B<set<int>>`, `C<set<int>>`, or `D<int>`, and a LHS expression of type `B<int>`
can be used in a type test where the RHS is `B<int>`, `C<int>`, or `E`. Those
are always allowed in compiled (and ghost) contexts.
For an expression `a` of type `A`, the expression `a is F<int>` is a ghost expression;
it can be used in ghost contexts, but not in compiled contexts.

For an expression `e` and type `t`, `e is t` is the condition determining whether
`e as t` is well-defined (but, as noted above, is not always a legal expression).

*The repertoire of types allowed in `is` tests may be expanded in the future.*

## 20.11. Unary Expressions

````grammar
UnaryExpression(allowLemma, allowLambda) =
  ( "-" UnaryExpression(allowLemma, allowLambda)
  | "!" UnaryExpression(allowLemma, allowLambda)
  | PrimaryExpression(allowLemma, allowLambda)
  )
````

A ``UnaryExpression`` applies either numeric ([Section 7.2](#sec-numeric-types))
or logical ([Section 7.1](#sec-booleans)) negation to its operand.

## 20.12. Primary Expressions
````grammar
PrimaryExpression(allowLemma, allowLambda) =
  ( NameSegment { Suffix }
  | LambdaExpression(allowLemma)
  | MapDisplayExpr { Suffix }
  | SeqDisplayExpr { Suffix }
  | SetDisplayExpr { Suffix }
  | EndlessExpression(allowLemma, allowLambda)
  | ConstAtomExpression { Suffix }
  )
````

After descending through all the binary and unary operators we arrive at
the primary expressions, which are explained in subsequent sections. As
can be seen, a number of these can be followed by 0 or more ``Suffix``es
to select a component of the value.

If the `allowLambda` is false then ``LambdaExpression``s are not
recognized in this context.

## 20.13. Lambda expressions {#sec-lambda-expressions}
````grammar
LambdaExpression(allowLemma) =
  ( WildIdent
  | "(" [ IdentTypeOptional { "," IdentTypeOptional } ] ")"
  )
  LambdaSpec
  "=>"
  Expression(allowLemma, allowLambda: true)
````

See [Section 5.4](#sec-lambda-specification) for a description of ``LambdaSpec``.

In addition to named functions, Dafny supports expressions that define
functions.  These are called _lambda (expression)s_ (some languages
know them as _anonymous functions_).  A lambda expression has the
form:
```dafny
( _params_ ) _specification_ => _body_
```
where _params_ is a comma-delimited list of parameter
declarations, each of which has the form `x` or `x: T`.  The type `T`
of a parameter can be omitted when it can be inferred.  If the
identifier `x` is not needed, it can be replaced by `_`.  If
_params_ consists of a single parameter `x` (or `_`) without an
explicit type, then the parentheses can be dropped; for example, the
function that returns the successor of a given integer can be written
as the following lambda expression:
```dafny
x => x + 1
```

The _specification_ is a list of clauses `requires E` or
`reads W`, where `E` is a boolean expression and `W` is a frame
expression.

_body_ is an expression that defines the function's return
value.  The body must be well-formed for all possible values of the
parameters that satisfy the precondition (just like the bodies of
named functions and methods).  In some cases, this means it is
necessary to write explicit `requires` and `reads` clauses.  For
example, the lambda expression
```dafny
x requires x != 0 => 100 / x
```
would not be well-formed if the `requires` clause were omitted,
because of the possibility of division-by-zero.

In settings where functions cannot be partial and there are no
restrictions on reading the heap, the _eta expansion_ of a function
`F: T -> U` (that is, the wrapping of `F` inside a lambda expression
in such a way that the lambda expression is equivalent to `F`) would
be written `x => F(x)`.  In Dafny, eta expansion must also account for
the precondition and reads set of the function, so the eta expansion
of `F` looks like:
```dafny
x requires F.requires(x) reads F.reads(x) => F(x)
```

## 20.14. Left-Hand-Side Expressions
````grammar
Lhs =
  ( NameSegment { Suffix }
  | ConstAtomExpression
    Suffix { Suffix }
  )
````

A left-hand-side expression is only used on the left hand
side of an [``UpdateStmt``](#sec-update-and-call-statement)
or an [Update with Failure Statement](#sec-update-failure).

An example of the first (`NameSegment`) form is:

```dafny
    LibraryModule.F().x
```

An example of the second (`ConstAtomExpression`) form is:

```dafny
    old(o.f).x
```

## 20.15. Right-Hand-Side Expressions
````grammar
Rhs =
  ( ArrayAllocation_
  | ObjectAllocation_
  | Expression(allowLemma: false, allowLambda: true)
  | HavocRhs_
  )
  { Attribute }
````

An ``Rhs`` is either array allocation, an object allocation,
an expression, or a havoc right-hand-side, optionally followed
by one or more ``Attribute``s.

Right-hand-side expressions appear in the following constructs:
[`ReturnStmt`](#sec-return-statement),
[`YieldStmt`](#sec-yield-statement),
[`UpdateStmt`](#sec-update-and-call-statement),
[`UpdateFailureStmt`](#sec-update-failure), or
[`VarDeclStatement`](#sec-var-decl-statement).
These are the only contexts in which arrays or objects may be
allocated, or in which havoc may be produced.

## 20.16. Array Allocation
````grammar
ArrayAllocation_ =
  "new" [ Type ] "[" [ Expressions ] "]"
  [ "(" Expression(allowLemma: true, allowLambda: true) ")"
  | "[" [ Expressions ] "]"
  ]
````

This allocates a new single or multi-dimensional array as explained in
section [Section 15](#sec-array-types).
The initialization portion is optional. One form is an
explicit list of values, in which case the dimension is optional:
```dafny
var a := new int[5];
var b := new int[5][2,3,5,7,11];
var c := new int[][2,3,5,7,11];
var d := new int[3][4,5,6,7]; // error
```
The comprehension form requires a dimension and uses a function of
type `nat -> T` where `T` is the array element type:
```dafny
var a := new int[5](i => i*i);
```
TODO: what about multi-dimensional arrays

## 20.17. Object Allocation
````grammar
ObjectAllocation_ = "new" Type [ "." TypeNameOrCtorSuffix ]
                               [ "(" [ Bindings ] ")" ]
````

This allocated a new object of a class type as explained
in section [Class Types](#sec-class-types).

## 20.18. Havoc Right-Hand-Side
````grammar
HavocRhs_ = "*"
````
A havoc right-hand-side produces an arbitrary value of its associated
type. To obtain a more constrained arbitrary value the "assign-such-that"
operator (`:|`) can be used. See [Section 19.6](#sec-update-and-call-statement).

## 20.19. Constant Or Atomic Expressions
````grammar
ConstAtomExpression =
  ( LiteralExpression
  | "this"
  | FreshExpression_
  | AllocatedExpression_
  | UnchangedExpression_
  | OldExpression_
  | CardinalityExpression_
  | ParensExpression
  )
````
A ``ConstAtomExpression`` represents either a constant of some type, or an
atomic expression. A ``ConstAtomExpression`` is never an l-value.

## 20.20. Literal Expressions
````grammar
LiteralExpression =
 ( "false" | "true" | "null" | Nat | Dec |
   charToken | stringToken )
````
A literal expression is a boolean literal, a null object reference,
an integer or real literal, a character or string literal,
or `this`, which denotes the current object in the context of
an instance method or function.

## 20.21. Fresh Expressions {#sec-fresh-expression}
````grammar
FreshExpression_ =
  "fresh" [ "@" LabelName ]
  "(" Expression(allowLemma: true, allowLambda: true) ")"
````

`fresh(e)` returns a boolean value that is true if
the objects denoted by expression `e` were all
freshly allocated since the time of entry to the enclosing method.

If the `LabelName` is present, it must denote a label that in the
enclosing method's control flow dominates the expression. In this
case, `fresh@L(e)` returns `true` if the objects denoted by `e` were all
freshly allocated since control flow reached label `L`.

The argument of `fresh` must be either an object reference
or a collection of object references.

## 20.22. Allocated Expressions
````grammar
AllocatedExpression_ =
  "allocated" "(" Expression(allowLemma: true, allowLambda: true) ")"
````

TO BE WRITTEN -- allocated predicate

## 20.23. Unchanged Expressions {#sec-unchanged-expression}

````grammar
UnchangedExpression_ =
  "unchanged" [ "@" LabelName ]
  "(" FrameExpression(allowLemma: true, allowLambda: true)
      { "," FrameExpression(allowLemma: true, allowLambda: true) }
  ")"
````

The `unchanged` expression returns `true` if and only if every reference
denoted by its arguments has the same value for all its fields in the
old and current state. For example, if `c` is an object with two
fields, `x` and `y`, then `unchanged(c)` is equivalent to
```dafny
c.x == old(c.x) && c.y == old(c.y)
```

Each argument to `unchanged` can be a reference, a set of references, or
a sequence of references. If it is a reference, it can be followed by
`` `f``, where `f` is a field of the reference. This form expresses that `f`,
not necessarily all fields, has the same value in the old and current
state.

The optional `@`-label says to use it as the old-state instead of using
the `old` state. That is, using the example `c` from above, the expression
`unchanged@Lbl(c)` is equivalent to
```dafny
c.x == old@Lbl(c.x) && c.y == old@Lbl(c.y)
```

Each reference denoted by the arguments of `unchanged` must be non-null and
must be allocated in the old-state of the expression.

## 20.24. Old and Old@ Expressions {#sec-old-expression}

````grammar
OldExpression_ =
  "old" [ "@" LabelName ]
  "(" Expression(allowLemma: true, allowLambda: true) ")"
````

An _old expression_ is used in postconditions or in the body of a method
or in the body or specification of any two-state function or two-state lemma;
an _old_ expression with a label is used only in the body of a method at a point
where the label dominates its use in this expression.

`old(e)` evaluates
the argument using the value of the heap on entry to the method;
`old@ident(e)` evaluates the argument using the value of the heap at the
given statement label.

Note that **old** and **old@** only affect heap dereferences,
like `o.f` and `a[i]`.
In particular, neither form has any effect on the value returned for local
variables or out-parameters (as they are not on the heap).[^Old]
If the value of an entire expression at a
particular point in the method body is needed later on in the method body,
the clearest means is to declare a ghost variable, initializing it to the
expression in question.

[^Old]: The semantics of `old` in Dafny differs from similar
constructs in other specification languages like ACSL or JML.

The argument of an `old` expression may not contain nested `old`,
[`fresh`](#sec-fresh-expression),
or [`unchanged`](#sec-unchanged-expression) expressions,
nor [two-state functions](#sec-two-state) or [two-state lemmas](#sec-two-state-lemma).

Here are some explanatory examples. All `assert` statements verify to be true.
```dafny
{% include_relative examples/Example-Old.dfy %}
```
```dafny
{% include_relative examples/Example-Old2.dfy %}
```
The next example demonstrates the interaction between `old` and array elements.
```dafny
{% include_relative examples/Example-Old3.dfy %}
```

## 20.25. Cardinality Expressions {#sec-cardinality-expression}
````grammar
CardinalityExpression_ =
  "|" Expression(allowLemma: true, allowLambda: true) "|"
````

For a finite-collection expression `c`, `|c|` is the cardinality of `c`. For a
finite set or sequence, the cardinality is the number of elements. For
a multiset, the cardinality is the sum of the multiplicities of the
elements. For a finite map, the cardinality is the cardinality of the
domain of the map. Cardinality is not defined for infinite sets or infinite maps.
For more, see [Section 10](#sec-collection-types).

## 20.26. Parenthesized Expression
````grammar
ParensExpression =
  "(" [ Expressions ] ")"
````
A ``ParensExpression`` is a list of zero or more expressions
enclosed in parentheses.

If there is exactly one expression enclosed then the value is just
the value of that expression.

If there are zero or more than one, the result is a `tuple` value.
See [Section 17.1](#sec-tuple-types).

## 20.27. Sequence Display Expression {#sec-seq-comprehension}
````grammar
SeqDisplayExpr =
  ( "[" [ Expressions ] "]"
  | "seq" [ GenericInstantiation ]
    "(" Expression(allowLemma: true, allowLambda: true)
    "," Expression(allowLemma: true, allowLambda: true)
    ")"
  )
````
A sequence display expression provides a way to construct
a sequence with given values. For example

```dafny
[1, 2, 3]
```
is a sequence with three elements in it.

```dafny
seq(k, n => n+1)
```
is a sequence of k elements whose values are obtained by evaluating the
second argument (a function) on the indices 0 up to k.

See section [#sec-sequences] for more information on
sequences.

## 20.28. Set Display Expression
````grammar
SetDisplayExpr =
  ( [ "iset" | "multiset" ] "{" [ Expressions ] "}"
  | "multiset" "(" Expression(allowLemma: true,
                              allowLambda: true) ")"
  )
````

A set display expression provides a way of constructing a set with given
elements. If the keyword `iset` is present, then a potentially infinite
set (with the finite set of given elements) is constructed.

For example

```dafny
{1, 2, 3}
```
is a set with three elements in it.
See [Section 10.1](#sec-sets) for more information on
sets.

A multiset display expression provides a way of constructing
a multiset with given elements and multiplicities. For example

```dafny
multiset{1, 1, 2, 3}
```
is a multiset with three elements in it. The number 1 has a multiplicity of 2,
and the numbers 2 and 3 each have a multiplicity of 1.

A multiset cast expression converts a set or a sequence
into a multiset as shown here:

```dafny
var s : set<int> := {1, 2, 3};
var ms : multiset<int> := multiset(s);
ms := ms + multiset{1};
var sq : seq<int> := [1, 1, 2, 3];
var ms2 : multiset<int> := multiset(sq);
assert ms == ms2;
```

See [Section 10.2](#sec-multisets) for more information on
multisets.

## 20.29. Map Display Expression {#sec-map-display-expression}
````grammar
MapDisplayExpr =
  ("map" | "imap" ) "[" [ MapLiteralExpressions ] "]"

MapLiteralExpressions =
  Expression(allowLemma: true, allowLambda: true)
  ":=" Expression(allowLemma: true, allowLambda: true)
  { "," Expression(allowLemma: true, allowLambda: true)
        ":=" Expression(allowLemma: true, allowLambda: true)
  }
````

A map display expression builds a finite or potentially infinite
map from explicit ``MapLiteralExpressions``. For example:

```dafny
var m := map[1 := "a", 2 := "b"];
ghost var im := imap[1 := "a", 2 := "b"];
```

See [Section 10.4](#sec-maps) for more details on maps and imaps.

## 20.30. Endless Expression
````grammar
EndlessExpression(allowLemma, allowLambda) =
  ( IfExpression(allowLemma, allowLambda)
  | MatchExpression(allowLemma, allowLambda)
  | QuantifierExpression(allowLemma, allowLambda)
  | SetComprehensionExpr(allowLemma, allowLambda)
  | StmtInExpr Expression(allowLemma, allowLambda)
  | LetExpression(allowLemma, allowLambda)
  | MapComprehensionExpr(allowLemma, allowLambda)
  )
````

``EndlessExpression`` gets it name from the fact that all its alternate
productions have no terminating symbol to end them, but rather they
all end with an ``Expression`` at the end. The various
``EndlessExpression`` alternatives are described below.

## 20.31. If Expression
````grammar
IfExpression(allowLemma, allowLambda) =
    "if" ( BindingGuard(allowLambda: true)
         | Expression(allowLemma: true, allowLambda: true)
         )
    "then" Expression(allowLemma: true, allowLambda: true)
    "else" Expression(allowLemma, allowLambda)
````

The ``IfExpression`` is a conditional expression. It first evaluates
the expression following the `if`. If it evaluates to `true` then
it evaluates the expression following the `then` and that is the
result of the expression. If it evaluates to `false` then the
expression following the `else` is evaluated and that is the result
of the expression. It is important that only the selected expression
is evaluated as the following example shows.

```dafny
var k := 10 / x; // error, may divide by 0.
var m := if x != 0 then 10 / x else 1; // ok, guarded
```

TO BE WRITTEN - binding form

## 20.32. Case and Extended Patterns {#sec-case-pattern}
````grammar
CasePattern =
  ( Ident "(" [ CasePattern { "," CasePattern } ] ")"
  | "(" [ CasePattern { "," CasePattern } ] ")"
  | IdentTypeOptional
  )

ExtendedPattern =
  ( PossiblyNegatedLiteralExpression
  | IdentTypeOptional
  | [ Ident ] "(" [ ExtendedPattern { "," ExtendedPattern } ] ")"
  )

PossiblyNegatedLiteralExpression =
  ( "-" ( Nat | Dec )
  | LiteralExpression
  )
````

Case patterns and extended patterns are used for (possibly nested)
pattern matching on inductive, coinductive or base type values.
The `ExtendedPattern` construct is used in
`CaseStatement` and `CaseExpression`s,
that is, in `match`
[statements](#sec-match-statement)
and [expressions](#sec-match-expression).
`CasePattern`s are used
in `LetExpr`s and `VarDeclStatement`s.
The `ExtendedPattern` differs from `CasePattern` is allowing literals
and symbolic constants.

When matching an inductive or coinductive value in
a ``MatchStmt`` or ``MatchExpression``, the ``ExtendedPattern``
must correspond to a

* (1) bound variable (a simple identifier),
* (2) a constructor of the type of the value,
* (3) a literal of the correct type, or
* (4) a symbolic constant.

If the extended pattern is

* a parentheses-enclosed possibly-empty list of patterns,
then the pattern matches a tuple.
* an identifier followed
by a parentheses-enclosed possibly-empty list of patterns, then the pattern
matches a constructor.
* a literal, then the pattern matches exactly that literal.
* a simple identifier, then the pattern matches
   * a parameter-less constructor if there is one defined with the correct type and the given name, else
   * the value of a symbolic constant, if a name lookup finds a declaration for
a constant with the given name (if the name is declared but with a non-matching type, a type resolution error will occur),
   * otherwise, the identifier is a new bound variable

Any ``ExtendedPattern``s inside the parentheses are then
matched against the arguments that were given to the
constructor when the value was constructed.
The number of ``ExtendedPattern`` must match the number
of parameters to the constructor (or the arity of the
tuple).
When matching a value of base type, the ``ExtendedPattern`` should
either be a ``LiteralExpression_`` of the same type as the value,
or a single identifier matching all values of this type.

The `ExtendedPattern`s and `CasePattern`s may be nested. The set of bound variable
identifiers contained in a `CaseBinding_` or `CasePattern` must be distinct.
They are bound to the corresponding values in the value being
matched. (Thus, for example, one cannot repeat a bound variable to
attempt to match a constructor that has two identical arguments.)

## 20.33. Match Expression {#sec-match-expression}

````grammar
MatchExpression(allowLemma, allowLambda) =
  "match" Expression(allowLemma, allowLambda)
  ( "{" { CaseExpression(allowLemma: true, allowLambda: true) } "}"
  | { CaseExpression(allowLemma, allowLambda) }
  )

CaseExpression(allowLemma, allowLambda) =
  "case" ExtendedPattern "=>" Expression(allowLemma, allowLambda)
````

A ``MatchExpression`` is used to conditionally evaluate and select an
expression depending on the value of an algebraic type, i.e. an inductive
type, a co-inductive type, or a base type.

The ``Expression`` following the `match` keyword is called the
_selector_. The selector is evaluated and then matched against each ``CaseExpression`` in order until a matching clause is found, as described in
the [section on `CaseBinding`s](#sec-case-pattern).

All of the variables in the ``CasePattern``s must be distinct.
If types for the identifiers are not given then types are inferred
from the types of the constructor's parameters. If types are
given then they must agree with the types of the
corresponding parameters.

A ``MatchExpression`` is evaluated by first evaluating the selector.
The ``ExtendedPattern``s of each ``CaseClause`` are then compared in order
 with the resulting value until a matching pattern is found.
If the constructor had
parameters then the actual values used to construct the selector
value are bound to the identifiers in the identifier list.
The expression to the right of the `=>` in the ``CaseClause`` is then
evaluated in the environment enriched by this binding. The result
of that evaluation is the result of the ``MatchExpression``.

Note that the braces enclosing the ``CaseClause``s may be omitted.

## 20.34. Quantifier Expression {#sec-quantifier-expression}
````grammar
QuantifierExpression(allowLemma, allowLambda) =
    ( "forall" | "exists" ) QuantifierDomain "::"
    Expression(allowLemma, allowLambda)

QuantifierDomain =
  IdentTypeOptional { "," IdentTypeOptional } { Attribute }
  [ "|" Expression(allowLemma: true, allowLambda: true) ]
````

A ``QuantifierExpression`` is a boolean expression that specifies that a
given expression (the one following the `::`) is true for all (for
**forall**) or some (for **exists**) combination of values of the
quantified variables, namely those in the ``QuantifierDomain``.

Here are some examples:
```dafny
assert forall x : nat | x <= 5 :: x * x <= 25;
(forall n :: 2 <= n ==> (exists d :: n < d < 2*n))
```

The quantifier identifiers are _bound_ within the scope of the
expressions in the ``QuantifierExpression``.

If types are not given for the quantified identifiers, then Dafny
attempts to infer their types from the context of the expressions.
It this is not possible, the program is in error.


## 20.35. Set Comprehension Expressions {#sec-set-comprehension-expression}
````grammar
SetComprehensionExpr(allowLemma, allowLambda) =
  [ "set" | "iset" ]
  IdentTypeOptional
  { "," IdentTypeOptional }
  { Attribute }
  "|"
  Expression(allowLemma, allowLambda)
  [ "::" Expression(allowLemma, allowLambda) ]
````

A set comprehension expression is an expression that yields a set
(possibly infinite if `iset` is used) that
satisfies specified conditions. There are two basic forms.

If there is only one quantified variable, the optional ``"::" Expression``
need not be supplied, in which case it is as if it had been supplied
and the expression consists solely of the quantified variable.
That is,

```dafny
set x : T | P(x)
```

is equivalent to

```dafny
set x : T | P(x) :: x
```

For the full form

```dafny
var S := set x1:T1, x2:T2 ... | P(x1, x2, ...) :: Q(x1, x2, ...)
```

the elements of `S` will be all values resulting from evaluation of `Q(x1, x2, ...)`
for all combinations of quantified variables `x1, x2, ...` such that
predicate `P(x1, x2, ...)` holds. For example,

```dafny
var S := set x:nat, y:nat | x < 2 && y < 2 :: (x, y)
```
yields `S == {(0, 0), (0, 1), (1, 0), (1,1) }`

The types on the quantified variables are optional and if not given Dafny
will attempt to infer them from the contexts in which they are used in the
`P` or `Q` expressions.

If a finite set was specified ("set" keyword used), Dafny must be able to prove that the
result is finite otherwise the set comprehension expression will not be
accepted.

Set comprehensions involving reference types such as

```dafny
set o: object | true
```

are allowed in ghost contexts. In particular, in ghost contexts, the
check that the result is finite should allow any set comprehension
where the bound variable is of a reference type. In non-ghost contexts,
it is not allowed, because--even though the resulting set would be
finite--it is not pleasant or practical to compute at run time.

The universe in which set comprehensions are evaluated is the set of all
_allocated_ objects, of the appropriate type and satisfying the given predicate.
For example, given

```dafny
class I {
  var i: int
}

method test() {
  ghost var m := set x: I :: 0 <= x.i <= 10;
}
```
the set `m` contains only those instances of `I` that have been allocated
at the point in program execution that `test` is evaluated. This could be
no instances, one per value of `x.i` in the stated range, multiple instances
of `I` for each value of `x.i`, or any other combination.

## 20.36. Statements in an Expression
````grammar
StmtInExpr = ( AssertStmt | AssumeStmt | ExpectStmt
             | RevealStmt | CalcStmt
             )
````

A ``StmtInExpr`` is a kind of statement that is allowed to
precede an expression in order to ensure that the expression
can be evaluated without error. For example:

```dafny
assume x != 0; 10/x
```

`Assert`, `assume`, `expect`, 'reveal' and `calc` statements can be used in this way.

## 20.37. Let Expression {#sec-let-expression}

````grammar
LetExpression(allowLemma, allowLambda) =
  (
    [ "ghost" ] "var" CasePattern { "," CasePattern }
    ( ":=" | ":-" | { Attribute } ":|" )
    Expression(allowLemma: false, allowLambda: true)
    { "," Expression(allowLemma: false, allowLambda: true) }
  |
    ":-"
    Expression(allowLemma: false, allowLambda: true)
  )
  ";"
  Expression(allowLemma, allowLambda)
````

A `let` expression allows binding of intermediate values to identifiers
for use in an expression. The start of the `let` expression is
signaled by the `var` keyword. They look much like a local variable
declaration except the scope of the variable only extends to the
enclosed expression.

For example:
```dafny
var sum := x + y; sum * sum
```

In the simple case, the ``CasePattern`` is just an identifier with optional
type (which if missing is inferred from the rhs).

The more complex case allows destructuring of constructor expressions.
For example:

```dafny
datatype Stuff = SCons(x: int, y: int) | Other
function GhostF(z: Stuff): int
  requires z.SCons?
{
  var SCons(u, v) := z; var sum := u + v; sum * sum
}
```

The syntax using `:-` is discussed in the following subsection.

## 20.38. Let or Fail Expression

The Let expression described in [Section 20.37](#sec-let-expression) has a failure variant
that simply uses `:-` instead of `:=`. This Let-or-Fail expression also permits propagating
failure results. However, in statements [Section 19.7](#sec-update-failure), failure results in
immediate return from the method; expressions do not have side effects or immediate return
mechanisms.

The expression `:- V; E` is desugared into the _expression_
```dafny
var tmp := V;
if tmp.IsFailure()
then tmp.PropagateFailure()
else E
```

The expression `var v :- V; E` is desugared into the _expression_
```dafny
var tmp := V;
if tmp.IsFailure()
then tmp.PropagateFailure()
else var v := tmp.Extract(); E
```

If the RHS is a list of expressions then the desugaring is similar. `var v, v1 :- V, V1; E` becomes
```dafny
var tmp := V;
if tmp.IsFailure()
then tmp.PropagateFailure()
else var v, v1 := tmp.Extract(), V1; E
```

So, if tmp is a failure value, then a corresponding failure value is propagated along; otherwise, the expression
is evaluated as normal.

Note that the value of the let-or-fail expression is either `tmp.PropagateFailure()` or `E`, the two sides of the
if-then-else expression. Consequently these two expressions must have types that can be joined into one type for
the whole let-or-fail expression. Typically that means that `tmp.PropagateFailure()` is a failure value and
`E` is a value-carrying success value, both of the same failure-compatible type, as described in [Section 19.7](#sec-update-failure).

TODO: Should the assert/assume/expect variants be permitted?

## 20.39. Map Comprehension Expression {#sec-map-comprehension-expression}
````grammar
MapComprehensionExpr(allowLemma, allowLambda) =
  ( "map" | "imap" )
  IdentTypeOptional
  { "," IdentTypeOptional }
  { Attribute }
  [ "|" Expression(allowLemma: true, allowLambda: true) ]
  "::"
  Expression(allowLemma, allowLambda)
  [ ":=" Expression(allowLemma, allowLambda) ]
````

A ``MapComprehensionExpr`` defines a finite or infinite map value
by defining a domain (using the ``IdentTypeOptional`` and the optional
condition following the "|") and for each value in the domain,
giving the mapped value using the expression following the "::".

For example:
```dafny
function square(x : int) : int { x * x }
method test()
{
  var m := map x : int | 0 <= x <= 10 :: x * x;
  ghost var im := imap x : int :: x * x;
  ghost var im2 := imap x : int :: square(x);
}
```

Dafny finite maps must be finite, so the domain must be constrained to be finite.
But imaps may be infinite as the example shows. The last example shows
creation of an infinite map that gives the same results as a function.

If the expression includes the `:=` token, that token separates
domain values from range values. For example, in the following code
```dafny
method test()
{
  var m := map x : int | 1 <= x <= 10 :: 2*x := 3*x;
}
```
`m` maps `2` to `3`, `4` to `6`, and so on.

## 20.40. Name Segment {#sec-name-segment}
````grammar
NameSegment = Ident [ GenericInstantiation | HashCall ]
````

A ``NameSegment`` names a Dafny entity by giving its declared
name optionally followed by information to
make the name more complete. For the simple case, it is
just an identifier.

If the identifier is for a generic entity, it is followed by
a ``GenericInstantiation`` which provides actual types for
the type parameters.

To reference a prefix predicate (see [Section 18.3.4](#sec-copredicates)) or
prefix lemma (see [Section 18.3.5.3](#sec-prefix-lemmas)), the identifier
must be the name of the copredicate or colemma and it must be
followed by a ``HashCall``.

## 20.41. Hash Call
````grammar
HashCall = "#" [ GenericInstantiation ]
  "[" Expression(allowLemma: true, allowLambda: true) "]"
  "(" [ Bindings ] ")"
````
A ``HashCall`` is used to call the prefix for a copredicate or colemma.
In the non-generic case, just insert `"#[k]"` before the call argument
list where k is the number of recursion levels.

In the case where the `colemma` is generic, the generic type
argument is given before. Here is an example:

```dafny
codatatype Stream<T> = Nil | Cons(head: int, stuff: T,
                                  tail: Stream<T>)

function append(M: Stream, N: Stream): Stream
{
  match M
  case Nil => N
  case Cons(t, s, M') => Cons(t, s, append(M', N))
}

function zeros<T>(s : T): Stream<T>
{
  Cons(0, s, zeros(s))
}

function ones<T>(s: T): Stream<T>
{
  Cons(1, s, ones(s))
}

copredicate atmost(a: Stream, b: Stream)
{
  match a
  case Nil => true
  case Cons(h,s,t) => b.Cons? && h <= b.head && atmost(t, b.tail)
}

colemma {:induction false} Theorem0<T>(s: T)
  ensures atmost(zeros(s), ones(s))
{
  // the following shows two equivalent ways to state the
  // co-inductive hypothesis
  if (*) {
    Theorem0#<T>[_k-1](s);
  } else {
    Theorem0(s);
  }
}

```

where the ``HashCall`` is `"Theorem0#<T>[_k-1](s);"`.
See [Section 18.3.4](#sec-copredicates) and [Section 18.3.5.3](#sec-prefix-lemmas).

## 20.42. Suffix
````grammar
Suffix =
  ( AugmentedDotSuffix_
  | DatatypeUpdateSuffix_
  | SubsequenceSuffix_
  | SlicesByLengthSuffix_
  | SequenceUpdateSuffix_
  | SelectionSuffix_
  | ArgumentListSuffix_
  )
````

The ``Suffix`` non-terminal describes ways of deriving a new value from
the entity to which the suffix is appended. There are six kinds
of suffixes which are described below.

### 20.42.1. Augmented Dot Suffix
````grammar
AugmentedDotSuffix_ = "." DotSuffix
                      [ GenericInstantiation | HashCall ]
````

An augmented dot suffix consists of a simple ``DotSuffix`` optionally
followed by either

* a ``GenericInstantiation`` (for the case where the item
selected by the ``DotSuffix`` is generic), or
* a ``HashCall`` for the case where we want to call a prefix copredicate
  or colemma. The result is the result of calling the prefix copredicate
  or colemma.

### 20.42.2. Datatype Update Suffix

````grammar
DatatypeUpdateSuffix_ =
  "." "(" MemberBindingUpdate { "," MemberBindingUpdate } ")"

MemberBindingUpdate =
  ( ident | digits )
  ":=" Expression(allowLemma: true, allowLambda: true)
````

A datatype update suffix is used to produce a new datatype value
that is the same as an old datatype value except that the
value corresponding to a given destructor has the specified value.
In a ``MemberBindingUpdate``, the ``ident`` or ``digits`` is the
name of a destructor (i.e. formal parameter name) for one of the
constructors of the datatype. The expression to the right of the
`:=` is the new value for that formal.

All of the destructors in a ``DatatypeUpdateSuffix_`` must be
for the same constructor, and if they do not cover all of the
destructors for that constructor then the datatype value being
updated must have a value derived from that same constructor.

Here is an example:

```dafny
module NewSyntax {
datatype MyDataType = MyConstructor(myint:int, mybool:bool)
                    | MyOtherConstructor(otherbool:bool)
                    | MyNumericConstructor(42:int)

method test(datum:MyDataType, x:int)
    returns (abc:MyDataType, def:MyDataType,
             ghi:MyDataType, jkl:MyDataType)
    requires datum.MyConstructor?
    ensures abc == datum.(myint := x + 2)
    ensures def == datum.(otherbool := !datum.mybool)
    ensures ghi == datum.(myint := 2).(mybool := false)
    // Resolution error: no non_destructor in MyDataType
    //ensures jkl == datum.(non_destructor := 5)
    ensures jkl == datum.(42 := 7)
{
    abc := MyConstructor(x + 2, datum.mybool);
    abc := datum.(myint := x + 2);
    def := MyOtherConstructor(!datum.mybool);
    ghi := MyConstructor(2, false);
    jkl := datum.(42 := 7);

    assert abc.(myint := abc.myint - 2) == datum.(myint := x);
}
}
```



### 20.42.3. Subsequence Suffix
````grammar
SubsequenceSuffix_ =
  "[" [ Expression(allowLemma: true, allowLambda: true) ]
      ".." [ Expression(allowLemma: true, allowLambda: true) ]
  "]"
````
A subsequence suffix applied to a sequence produces a new sequence whose
elements are taken from a contiguous part of the original sequence. For
example, expression `s[lo..hi]` for sequence `s`, and integer-based
numerics `lo` and `hi` satisfying `0 <= lo <= hi <= |s|`. See
section [#sec-other-sequence-expressions] for details.

### 20.42.4. Slices By Length Suffix
````grammar
SlicesByLengthSuffix_ =
  "[" Expression(allowLemma: true, allowLambda: true) ":"
      [
        Expression(allowLemma: true, allowLambda: true)
        { ":" Expression(allowLemma: true, allowLambda: true) }
        [ ":" ]
      ]
  "]"
````

Applying a ``SlicesByLengthSuffix_`` to a sequence produces a
sequence of subsequences of the original sequence.
See section [#sec-other-sequence-expressions] for details.

### 20.42.5. Sequence Update Suffix
````grammar
SequenceUpdateSuffix_ =
  "[" Expression(allowLemma: true, allowLambda: true)
      ":=" Expression(allowLemma: true, allowLambda: true)
  "]"
````

For a sequence `s` and expressions `i` and `v`, the expression
`s[i := v]` is the same as the sequence `s` except that at
index `i` it has value `v`.

If the type of `s` is `seq<T>`, then `v` must have type `T`.
The index `i` can have any integer- or bit-vector-based type
(this is one situation in which Dafny implements implicit
conversion, as if an `as int` were appended to the index expression).
The expression `s[i := v]` has the same type as `s`.

### 20.42.6. Selection Suffix
````grammar
SelectionSuffix_ =
  "[" Expression(allowLemma: true, allowLambda: true)
      { "," Expression(allowLemma: true, allowLambda: true) }
  "]"
````

If a ``SelectionSuffix_`` has only one expression in it, it is a
zero-based index that may be used to select a single element of a
sequence or from a single-dimensional array.

If a ``SelectionSuffix_`` has more than one expression in it, then
it is a list of indices to index into a multi-dimensional array.
The rank of the array must be the same as the number of indices.

If the ``SelectionSuffix_`` is used with an array or a sequence,
then each index expression can have any integer- or bit-vector-based
type
(this is one situation in which Dafny implements implicit
conversion, as if an `as int` were appended to the index expression).

### 20.42.7. Argument List Suffix
````grammar
ArgumentListSuffix_ = "(" [ Expressions ] ")"
````

An argument list suffix is a parenthesized list of expressions that
are the arguments to pass to a method or function that is being
called. Applying such a suffix causes the method or function
to be called and the result is the result of the call.

## 20.43. Expression Lists
````grammar
Expressions =
    Expression(allowLemma: true, allowLambda: true)
    { "," Expression(allowLemma: true, allowLambda: true) }
````

The ``Expressions`` non-terminal represents a list of
one or more expressions separated by commas.

## 20.44. Parameter Bindings

Method calls, object-allocation calls (`new`), function calls, and
datatype constructors can be called with both positional arguments
and named arguments.
````grammar
ActualBindings =
    ActualBinding
    { "," ActualBinding }

ActualBinding =
    [ NoUSIdentOrDigits ":=" ]
    Expression(allowLemma: true, allowLambda: true)
````

Positional arguments must be given before any named arguments.
Positional arguments are passed to the formals in the corresponding
position. Named arguments are passed to the formal of the given
name. Named arguments can be given out of order from how the corresponding
formal parameters are declared. A formal declared with the modifier
`nameonly` is not allowed to be passed positionally.
The list of bindings for a call must
provide exactly one value for every required parameter and at most one
value for each optional parameter, and must never name
non-existent formals. Any optional parameter that is not given a value
takes on the default value declared in the callee for that optional parameter.

## 20.45. Formal Parameters and Default-Value Expressions

The formal parameters of a method, constructor in a class, iterator,
function, or datatype constructor can be declared with an expression
denoting a _default value_. This makes the parameter _optional_,
as opposed to _required_. All required parameters must be declared
before any optional parameters. All nameless parameters in a datatype
constructor must be declared before any `nameonly` parameters.

The default-value expression for a parameter is allowed to mention the
other parameters, including `this` (for instance methods and instance
functions), but not the implicit `_k` parameter in least and greatest
predicates and lemmas. The default value of a parameter may mention
both preceding and subsequent parameters, but there may not be any
dependent cycle between the parameters and their default-value
expressions.

The well-formedness of default-value expressions is checked independent
of the precondition of the enclosing declaration. For a function, the
parameter default-value expressions may only read what the function's
`reads` clause allows. For a datatype constructor, parameter default-value
expressions may not read anything. A default-value expression may not be
involved in any recursive or mutually recursive calls with the enclosing
declaration.

## 20.46. Compile-Time Constants {#sec-compile-time-constants}

In certain situations in Dafny it is helpful to know what the value of a
constant is during program analysis, before verification or execution takes
place. For example, a compiler can choose an optimized representation of a
`newtype` that is a subset of `int` if it knows the range of possible values
of the subset type: if the range is within 0 to less than 256, then an
unsigned 8-bit representation can be used.

To continue this example, suppose a new type is defined as
```
const MAX := 47
newtype mytype = x | 0 <= x < MAX*4
```
In this case, we would prefer that Dafny recognize that `MAX*4` is
known to be constant with a value of `188`. The kinds of expressions
for which such an optimization is possible are called
_compile-time constants_. Note that the representation of `mytype` makes
no difference semantically, but can affect how compiled code is represented at run time.
In addition, though, using a symbolic constant (which may
well be used elsewhere as well) improves the self-documentation of the code.

In Dafny, the following expressions are compile-time constants[^CTC], recursively
(that is, the arguments of any operation must themselves be compile-time constants):

- int, bit-vector, real, boolean, char and string literals
- int operations: `+ - * / %` and unary `-` and comparisons `< <= > >= == !=`
- real operations: `+ - *` and unary `-` and comparisons `< <= > >= == !='
- bool operations: `&& || ==> <== <==> == !=` and unary '!'
- bit-vector operations: `+ - * / % << >> & | ^` and unary `! -` and comparisons `< <= > >= == !=`
- char operations: `< <= > >= == !=`
- string operations: length: `|...|`, concatenation: `+`, comparisons `< <= == !=`, indexing `[]`
- conversions between: `int` `real` `char` bit-vector
- newtype operations: newtype arguments, but not newtype results
- symbolic values that are declared `const` and have an explicit initialization value that is a compile-time constant
- conditional (if-then-else) expressions
- parenthesized expressions

[^CTC]: This set of operations that are constant-folded may be enlarged in
future versions of Dafny.

