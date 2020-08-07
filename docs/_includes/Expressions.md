# Expressions
The grammar of Dafny expressions follows a hierarchy that
reflects the precedence of Dafny operators. The following
table shows the Dafny operators and their precedence
in order of increasing binding power.
```
+--------------------------+------------------------------------+
| operator                 | description                        |
+--------------------------+------------------------------------+
| `;`                      | In LemmaCall;Expression            |
+--------------------------+------------------------------------+
| `<==>`, &hArr;           | equivalence (if and only if)       |
+--------------------------+------------------------------------+
| `==>`, &rArr;            | implication (implies)              |
| `<==`, &lArr;            | reverse implication (follows from) |
+--------------------------+------------------------------------+
| `&&`, &and;              | conjunction (and)                  |
| [\|\|]{.monospace}, &or; | disjunction (or)                   |
+--------------------------+------------------------------------+
| `==`                     | equality                           |
| `==#[k]`                 | prefix equality (co-inductive)     |
| `!=`                     | disequality                        |
| `!=#[k]`                 | prefix disequality (co-inductive)  |
| `<`                      | less than                          |
| `<=`                     | at most                            |
| `>=`                     | at least                           |
| `>`                      | greater than                       |
| `in`                     | collection membership              |
| `!in`                    | collection non-membership          |
| `!!`                     | disjointness                       |
+--------------------------+------------------------------------+
| `+`                      | addition (plus)                    |
| `-`                      | subtraction (minus)                |
+--------------------------+------------------------------------+
| `*`                      | multiplication (times)             |
| `/`                      | division (divided by)              |
| `%`                      | modulus (mod)                      |
+--------------------------+------------------------------------+
| `-`                      | arithmetic negation (unary minus)  |
| `!`, &not;               | logical negation                   |
| Primary Expressions      |                                    |
+--------------------------+------------------------------------+
```
We are calling the ``UnaryExpression``s that are neither
arithmetic nor logical negation the _primary expressions_.
They are the most tightly bound.

In the grammar entries below we explain the meaning when the
operator for that precedence level is present. If the
operator is not present then we just descend to the
next precedence level.

## Top-level expressions
````
Expression(allowLemma, allowLambda) =
    EquivExpression(allowLemma, allowLambda)
    [ ";" Expression(allowLemma, allowLambda) ]
````

The "allowLemma" argument says whether or not the expression
to be parsed is allowed to have the form S;E where S is a call to a lemma.
"allowLemma" should be passed in as "false" whenever the expression to
be parsed sits in a context that itself is terminated by a semi-colon.

The "allowLambda" says whether or not the expression to be parsed is
allowed to be a lambda expression.  More precisely, an identifier or
parenthesized-enclosed comma-delimited list of identifiers is allowed to
continue as a lambda expression (that is, continue with a "reads", "requires",
or "=>") only if "allowLambda" is true.  This affects function/method/iterator
specifications, if/while statements with guarded alternatives, and expressions
in the specification of a lambda expression itself.

Sometimes an expression will fail unless some relevant fact is known.
In the following example the `F_Fails` function fails to verify
because the `Fact(n)` divisor may be zero. But preceding
the expression by a lemma that ensures that the denominator
is not zero allows function `F_Succeeds` to succeed.
```
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

## Equivalence Expressions
````
EquivExpression(allowLemma, allowLambda) =
  ImpliesExpliesExpression(allowLemma, allowLambda)
  { "<==>" ImpliesExpliesExpression(allowLemma, allowLambda) }
````
An ``EquivExpression`` that contains one or more "<==>"s is
a boolean expression and all the contained ``ImpliesExpliesExpression``
must also be boolean expressions. In that case each "<==>"
operator tests for logical equality which is the same as
ordinary equality.

See section [#sec-equivalence-operator] for an explanation of the
`<==>` operator as compared with the `==` operator.

## Implies or Explies Expressions
````
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

See section [#sec-implication-and-reverse-implication] for an explanation
of the `==>` and `<==` operators.

## Logical Expressions

````
LogicalExpression(allowLemma, allowLambda) =
  RelationalExpression(allowLemma, allowLambda)
  [ ( "&&" RelationalExpression(allowLemma, allowLambda)
           { "&&" RelationalExpression(allowLemma, allowLambda) }
    | "||" RelationalExpression(allowLemma, allowLambda)
           { "||" RelationalExpression(allowLemma, allowLambda) }
    )
  ]
````

See section [#sec-conjunction-and-disjunction] for an explanation
of the `&&` (or &and;) and `||` (or &or;) operators.

## Relational Expressions
````
RelationalExpression(allowLemma, allowLambda) =
  Term(allowLemma, allowLambda)
  { RelOp Term(allowLemma, allowLambda) }

RelOp =
  ( "==" [ "#" "[" Expression(allowLemma: true, allowLambda: true) "]" ]
  | "<" | ">" | "<=" | ">="
  | "!=" [ "#" "[" Expression(allowLemma: true, allowLambda: true) "]" ]
  | "in"
  | "!in"
  | "!!"
  )

````

The relation expressions that have a ``RelOp`` compare two or more terms.
As explained in section [#sec-basic-types], `==`, `!=`, ``<``, `>`, `<=`, and `>=`
and their corresponding Unicode equivalents are _chaining_.

The `in` and `!in` operators apply to collection types as explained in
section [#sec-collection-types] and represent membership or non-membership
respectively.

The `!!` represents disjointness for sets and multisets as explained in
sections [#sec-sets] and [#sec-multisets].

Note that `x ==#[k] y` is the prefix equality operator that compares
co-inductive values for equality to a nesting level of k, as
explained in section [#sec-co-equality].

## Terms
````
Term(allowLemma, allowLambda) =
  Factor(allowLemma, allowLambda)
  { AddOp Factor(allowLemma, allowLambda) }
AddOp = ( "+" | "-" )
````

`Terms` combine `Factors` by adding or subtracting.
Addition has these meanings for different types:

* Arithmetic addition for numeric types (section [#sec-numeric-types]).
* Union for sets and multisets (sections [#sec-sets] and [#sec-multisets])
* Concatenation for sequences (section [#sec-sequences])

Subtraction is arithmetic subtraction for numeric types, and set or multiset
difference for sets and multisets.

## Factors
````
Factor(allowLemma, allowLambda) =
  UnaryExpression(allowLemma, allowLambda)
  { MulOp UnaryExpression(allowLemma, allowLambda) }
MulOp = ( "*" | "/" | "%" )
````

A ``Factor`` combines ``UnaryExpression``s using multiplication,
division, or modulus. For numeric types these are explained in
section [#sec-numeric-types].

Only `*` has a non-numeric application. It represents set or multiset
intersection as explained in sections [#sec-sets] and [#sec-multisets].

## Unary Expressions

````
UnaryExpression(allowLemma, allowLambda) =
  ( "-" UnaryExpression(allowLemma, allowLambda)
  | "!" UnaryExpression(allowLemma, allowLambda)
  | PrimaryExpression_(allowLemma, allowLambda)
  )

````

A ``UnaryExpression`` applies either numeric (section [#sec-numeric-types])
or logical (section [#sec-booleans]) negation to its operand.

## Primary Expressions
<!-- These are introduced for explanatory purposes as are not in the grammar. -->
````
PrimaryExpression_(allowLemma, allowLambda) =
  ( NameSegment { Suffix }
  | LambdaExpression(allowLemma)
  | MapDisplayExpr { Suffix }
  | SeqDisplayExpr { Suffix }
  | SetDisplayExpr { Suffix }
  | MultiSetExpr { Suffix }
  | EndlessExpression(allowLemma, allowLambda)
  | ConstAtomExpression { Suffix }
  )

````

After descending through all the binary and unary operators we arrive at
the primary expressions which are explained in subsequent sections. As
can be seen, a number of these can be followed by 0 or more ``Suffix``es
to select a component of the value.

If the `allowLambda` is false then ``LambdaExpression``s are not
recognized in this context.

## Lambda expressions
````
LambdaExpression(allowLemma) =
  ( WildIdent
  | "(" [ IdentTypeOptional { "," IdentTypeOptional } ] ")"
  )
  LambdaSpec_
  "=>" Expression(allowLemma, allowLambda: true)
````

See section [#sec-lambda-specification] for a description of ``LambdaSpec``.

In addition to named functions, Dafny supports expressions that define
functions.  These are called _lambda (expression)s_ (some languages
know them as _anonymous functions_).  A lambda expression has the
form:
```
(\(_params_\)) \(_specification_\) => \(_body_\)
```
where `\(_params_\)` is a comma-delimited list of parameter
declarations, each of which has the form `x` or `x: T`.  The type `T`
of a parameter can be omitted when it can be inferred.  If the
identifier `x` is not needed, it can be replaced by "`_`".  If
`\(_params_\)` consists of a single parameter `x` (or `_`) without an
explicit type, then the parentheses can be dropped; for example, the
function that returns the successor of a given integer can be written
as the following lambda expression:
```
x => x + 1
```

The `\(_specification_\)` is a list of clauses `requires E` or
`reads W`, where `E` is a boolean expression and `W` is a frame
expression.

`\(_body_\)` is an expression that defines the function's return
value.  The body must be well-formed for all possible values of the
parameters that satisfy the precondition (just like the bodies of
named functions and methods).  In some cases, this means it is
necessary to write explicit `requires` and `reads` clauses.  For
example, the lambda expression
```
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
```
x requires F.requires(x) reads F.reads(x) => F(x)
```

## Left-Hand-Side Expressions
````
Lhs =
  ( NameSegment { Suffix }
  | ConstAtomExpression Suffix { Suffix }
  )
````

A left-hand-side expression is only used on the left hand
side of an ``UpdateStmt``.

An example of the first (`NameSegment`) form is:

```
    LibraryModule.F().x
```

An example of the second (`ConstAtomExpression`) form is:

```
    old(o.f).x
```

## Right-Hand-Side Expressions
````
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
``ReturnStmt``, ``YieldStmt``, ``UpdateStmt``, or ``VarDeclStatement``.
These are the only contexts in which arrays or objects may be
allocated, or in which havoc may be produced.

## Array Allocation
````
ArrayAllocation_ = "new" Type "[" Expressions "]"
````

This allocates a new single or multi-dimensional array as explained in
section [#sec-array-types].

## Object Allocation
````
ObjectAllocation_ = "new" Type [ "(" [ Expressions ] ")" ]
````

This allocated a new object of a class type as explained
in section [#sec-class-types].

## Havoc Right-Hand-Side
````
HavocRhs_ = "*"
````
A havoc right-hand-side produces an arbitrary value of its associated
type. To get a more constrained arbitrary value the "assign-such-that"
operator (`:|`) can be used. See section [#sec-update-and-call-statements].

## Constant Or Atomic Expressions
````
ConstAtomExpression =
  ( LiteralExpression_
  | FreshExpression_
  | OldExpression_
  | CardinalityExpression_
  | NumericConversionExpression_
  | ParensExpression
  )
````
A ``ConstAtomExpression`` represent either a constant of some type, or an
atomic expression. A ``ConstAtomExpression`` is never an l-value.
## Literal Expressions
````
LiteralExpression_ =
 ( "false" | "true" | "null" | Nat | Dec |
   charToken | stringToken | "this")
````
A literal expression is a boolean literal, a null object reference,
an unsigned integer or real literal, a character or string literal,
or "this" which denote the current object in the context of
an instance method or function.

## Fresh Expressions
````
FreshExpression_ = "fresh" "(" Expression(allowLemma: true, allowLambda: true) ")"
````

`fresh(e)` returns a boolean value that is true if
the objects referenced in expression `e` were all
freshly allocated in the current method invocation.
The argument of `fresh` must be either an object reference
or a collection of object references.

## Old Expressions
````
OldExpression_ = "old" "(" Expression(allowLemma: true, allowLambda: true) ")"
````

An _old expression_ is used in postconditions. `old(e)` evaluates to
the value expression `e` had on entry to the current method.
Note that **old** only affects heap dereferences, like `o.f` and `a[i]`.
In particular, **old** has no effect on the value returned for local
variables or out-parameters.

## Cardinality Expressions
````
CardinalityExpression_ = "|" Expression(allowLemma: true, allowLambda: true) "|"
````

For a finite-collection expression `c`, `|c|` is the cardinality of `c`. For a
finite set or sequence, the cardinality is the number of elements. For
a multiset, the cardinality is the sum of the multiplicities of the
elements. For a finite map, the cardinality is the cardinality of the
domain of the map. Cardinality is not defined for infinite sets or infinite maps.
For more, see section [#sec-collection-types].

## Numeric Conversion Expressions
````
NumericConversionExpression_ =
    ( "int" | "real" ) "(" Expression(allowLemma: true, allowLambda: true) ")"
````
Numeric conversion expressions give the name of the target type
followed by the expression being converted in parentheses.
This production is for `int` and `real` as the target types
but this also applies more generally to other numeric types,
e.g. `newtypes`. See section [#sec-numeric-conversion-operations].

## Parenthesized Expression
````
ParensExpression =
  "(" [ Expressions ] ")"
````
A ``ParensExpression`` is a list of zero or more expressions
enclosed in parentheses.

If there is exactly one expression enclosed then the value is just
the value of that expression.

If there are zero or more than one, the result is a `tuple` value.
See section [#sec-tuple-types].

## Sequence Display Expression
````
SeqDisplayExpr = "[" [ Expressions ] "]"
````
A sequence display expression provide a way to constructing
a sequence with given values. For example

```
[1, 2, 3]
```
is a sequence with three elements in it.
See section [#sec-sequences] for more information on
sequences.

## Set Display Expression
````
SetDisplayExpr = [ "iset" ] "{" [ Expressions ] "}"
````

A set display expression provides a way of constructing a set with given
elements. If the keyword `iset` is present, then a potentially infinite
set (with the finiite set of given elements) is constructed.

For example

```
{1, 2, 3}
```
is a set with three elements in it.
See section [#sec-sets] for more information on
sets.

## Multiset Display or Cast Expression
````
MultiSetExpr =
    "multiset"
    ( "{" [ Expressions ] "}"
    | "(" Expression(allowLemma: true, allowLambda: true) ")"
    )
````

A multiset display expression provides a way of constructing
a multiset with given elements and multiplicities. For example

```
multiset{1, 1, 2, 3}
```
is a multiset with three elements in it. The number 1 has a multiplicity of 2,
the others a multiplicity of 1.

On the other hand, a multiset cast expression converts a set or a sequence
into a multiset as shown here:

```
var s : set<int> := {1, 2, 3};
var ms : multiset<int> := multiset(s);
ms := ms + multiset{1};
var sq : seq<int> := [1, 1, 2, 3];
var ms2 : multiset<int> := multiset(sq);
assert ms == ms2;
```

See section [#sec-multisets] for more information on
multisets.

## Map Display Expression
````
MapDisplayExpr = ("map" | "imap" ) "[" [ MapLiteralExpressions ] "]"
MapLiteralExpressions =
    Expression(allowLemma: true, allowLambda: true)
    ":=" Expression(allowLemma: true, allowLambda: true)
    { "," Expression(allowLemma: true, allowLambda: true)
          ":=" Expression(allowLemma: true, allowLambda: true)
    }
````

A map display expression builds a finite or potentially infinite
map from explicit ``MapLiteralExpressions``. For example:

```
var m := map[1 := "a", 2 := "b"];
ghost var im := imap[1 := "a", 2 := "b"];
```

See section [#sec-finite-and-infinite-maps] for more details on maps and imaps.

## Endless Expression
````
EndlessExpression(allowLemma, allowLambda) =
  ( IfExpression_(allowLemma, allowLambda)
  | MatchExpression(allowLemma, allowLambda)
  | QuantifierExpression(allowLemma, allowLambda)
  | SetComprehensionExpr(allowLemma, allowLambda)
  | StmtInExpr Expression(allowLemma, allowLambda)
  | LetExpr(allowLemma, allowLambda)
  | MapComprehensionExpr(allowLemma, allowLambda)
  )
````
<!-- Experimental - do not document.
  | NamedExpr(allowLemma, allowLambda)
-->

``EndlessExpression`` gets it name from the fact that all its alternate
productions have no terminating symbol to end them, but rather they
all end with an ``Expression`` at the end. The various
``EndlessExpression`` alternatives are described below.

## If Expression
````
IfExpression_(allowLemma, allowLambda) =
    "if" Expression(allowLemma: true, allowLambda: true)
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

```
var k := 10 / x; // error, may divide by 0.
var m := if x != 0 then 10 / x else 1; // ok, guarded
```

## Case Bindings, Patterns, and Extended Patterns
````
CaseBinding_ =
  "case"
  ( ExtendedPattern
  | "(" [ ExtendedPattern { "," ExtendedPattern } ] ")"
  )

CasePattern =
  ( Ident "(" [ CasePattern { "," CasePattern } ] ")"
  | "(" [ CasePattern { "," Casepattern } ] ")"
  | IdentTypeOptional
  )


ExtendedPattern =
  ( LiteralExpression_
  ( Ident [ "(" ExtendedPattern { "," ExtendedPattern } ")" ]
````

Case bindings and extended patterns are used for (possibly nested)
pattern matching on inductive, coinductive or base type values.
The ``CaseBinding_`` construct is used in
``CaseStatement`` and ``CaseExpression``s.
``CasePattern``s are used
in ``LetExpr``s and ``VarDeclStatement``s.

When matching an inductive or coinductive value in
a ``MatchStmt`` or ``MatchExpression``, the ``ExtendedPattern``
must either correspond to a constructor of the type of the value,
or a bound variable. A tuple is
considered to have a single constructor.
The ``Ident`` of the ``CaseBinding_`` must either match the name
of a constructor (or in the case of a tuple, the ``Ident`` is
absent and the second alternative is chosen), or not be applied to a tuple of ``ExtendedPattern``.
The ``ExtendedPattern``s inside the parentheses are then
matched against the arguments that were given to the
constructor when the value was constructed.
The number of ``ExtendedPattern`` must match the number
of parameters to the constructor (or the arity of the
tuple).
When matching a value of base type, the ``ExtendedPattern`` should
either be a ``LiteralExpression_`` of the same type as the value,
or a single identifier matching all values of this type.

The ``CasePattern``s may be nested. The set of non-constructor-name
identifiers contained in a ``CaseBinding_`` must be distinct.
They are bound to the corresponding values in the value being
matched.

## Match Expression

````
MatchExpression(allowLemma, allowLambda) =
  "match" Expression(allowLemma, allowLambda)
  ( "{" { CaseExpression(allowLemma: true, allowLambda: true) } "}"
  | { CaseExpression(allowLemma, allowLambda) }
  )

CaseExpression(allowLemma, allowLambda) =
    CaseBinding_ "=>" Expression(allowLemma, allowLambda)
````

A ``MatchExpression`` is used to conditionally evaluate and select an
expression depending on the value of an algebraic type, i.e. an inductive
type, a co-inductive type, or a base type.

The ``Expression`` following the `match` keyword is called the
_selector_. The selector is evaluated and then matched against each ``CaseExpression`` in order until a matching clause is found. An ``Ident`` following the `case` keyword in a
``CaseExpression`` is either the name of a constructor of the selector's type, or a bound variable.
It may be absent if the expression being matched is a tuple since these
have no constructor name.

If the constructor has parameters then in the ``CaseExpression`` the
constructor name must be followed by a parenthesized list of ``CasePattern``s
with one ``CasePattern`` for each constructor parameter.

If the constructor has no parameters then the
``CaseExpression`` must not have a following ``CasePattern`` list (though
optional empty parentheses are allowed).

All of the variables in the ``CasePattern``s must be distinct.
If types for the identifiers are not given then types are inferred
from the types of the constructor's parameters. If types are
given then they must agree with the types of the
corresponding parameters.

A ``MatchExpression`` is evaluated by first evaluating the selector.
The ``ExtendedPattern`` of each ``CaseClause`` are then compared in order
 with the resulting value until a matching pattern is found.
If the constructor had
parameters then the actual values used to construct the selector
value are bound to the identifiers in the identifier list.
The expression to the right of the `=>` in the ``CaseClause`` is then
evaluated in the environment enriched by this binding. The result
of that evaluation is the result of the ``MatchExpression``.

Note that the braces enclosing the ``CaseClause``s may be omitted.

## Quantifier Expression
````
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
```
assert forall x : nat | x <= 5 :: x * x <= 25;
(forall n :: 2 <= n ==> (exists d :: n < d < 2*n))
```

or using the Unicode symbols:
<pre><code>
assert &forall; x : nat | x <= 5 &bull; x * x <= 25;
(&forall; n &bull; 2 <= n ==> (&exist; d &bull; n < d < 2*n))
</code></pre>

The quantifier identifiers are _bound_ within the scope of the
expressions in the ``QuantifierExpression``.

If types are not given for the quantified identifiers, then Dafny
attempts to infer their types from the context of the expressions.
It this is not possible, the program is in error.


## Set Comprehension Expressions
````
SetComprehensionExpr(allowLemma, allowLambda) =
  [ "set" | "iset" ]
  IdentTypeOptional { "," IdentTypeOptional } { Attribute }
  "|" Expression(allowLemma, allowLambda)
  [ "::" Expression(allowLemma, allowLambda) ]
````

A set comprehension expression is an expressions that yields a set
(possibly infinite if `iset` is used) that
satisfies specified conditions. There are two basic forms.

If there is only one quantified variable, the optional ``"::" Expression``
need not be supplied, in which case it is as if it had been supplied
and the expression consists solely of the quantified variable.
That is,

```
set x : T | P(x)
```

is equivalent to

```
set x : T | P(x) :: x
```

For the full form

```
var S := set x1:T1, x2:T2 ... | P(x1, x2, ...) :: Q(x1, x2, ...)
```

the elements of `S` will be all values resulting from evaluation of `Q(x1, x2, ...)`
for all combinations of quantified variables `x1, x2, ...` such that
predicate `P(x1, x2, ...)` holds. For example,

```
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

```
set o: object | true
```

are allowed in ghost contexts. In particular, in ghost contexts, the
check that the result is finite should allow any set comprehension
where the bound variable is of a reference type. In non-ghost contexts,
it is not allowed, because--even though the resulting set would be
finite--it is not pleasant or practical to compute at run time.

## Statements in an Expression
````
StmtInExpr = ( AssertStmt | AssumeStmt | CalcStmt )
````

A ``StmtInExpr`` is a kind of statement that is allowed to
precede an expression in order to ensure that the expression
can be evaluated without error. For example:

```
assume x != 0; 10/x
```

`Assert`, `assume` and `calc` statements can be used in this way.

## Let Expression

````
LetExpr(allowLemma, allowLambda) =
    [ "ghost" ] "var" CasePattern { "," CasePattern }
    ( ":=" | { Attribute } ":|" )
    Expression(allowLemma: false, allowLambda: true)
    { "," Expression(allowLemma: false, allowLambda: true) } ";"
    Expression(allowLemma, allowLambda)
````

A `let` expression allows binding of intermediate values to identifiers
for use in an expression. The start of the `let` expression is
signaled by the `var` keyword. They look much like a local variable
declaration except the scope of the variable only extends to the
enclosed expression.

For example:
```
var sum := x + y; sum * sum
```

In the simple case, the ``CasePattern`` is just an identifier with optional
type (which if missing is inferred from the rhs).

The more complex case allows destructuring of constructor expressions.
For example:

```
datatype Stuff = SCons(x: int, y: int) | Other
function GhostF(z: Stuff): int
  requires z.SCons?
{
  var SCons(u, v) := z; var sum := u + v; sum * sum
}
```

## Map Comprehension Expression
````
MapComprehensionExpr(allowLemma, allowLambda) =
  ( "map" | "imap" ) IdentTypeOptional { Attribute }
  [ "|" Expression(allowLemma: true, allowLambda: true) ]
  "::" Expression(allowLemma, allowLambda)
````

A ``MapComprehensionExpr`` defines a finite or infinite map value
by defining a domain (using the ``IdentTypeOptional`` and the optional
condition following the "|") and for each value in the domain,
giving the mapped value using the expression following the "::".

For example:
```
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

<!-- Experimental - do not document.

## Named Expression
````
NamedExpr(allowLemma, allowLambda) =
    "label" LabelName ":" Expression(allowLemma, allowLambda)
````

A ``NamedExpr`` is an expression that has been tagged with a name.
For example:
```
label squareit: x * x
```

This is an experimental feature.
TODO: When is this useful. Is there any way to refer to the label?
Should we remove the description?
-->

## Name Segment
````
NameSegment = Ident [ GenericInstantiation | HashCall ]
````

A ``NameSegment`` names a Dafny entity by giving its declared
name optionally followed by information to
make the name more complete. For the simple case, it is
just an identifier.

If the identifier is for a generic entity, it is followed by
a ``GenericInstantiation`` which provides actual types for
the type parameters.

To reference a prefix predicate (see section [#sec-copredicates]) or
prefix lemma (see section [#sec-prefix-lemmas]), the identifier
must be the name of the copredicate or colemma and it must be
followed by a ``HashCall``.

## Hash Call
````
HashCall = "#" [ GenericInstantiation ]
  "[" Expression(allowLemma: true, allowLambda: true) "]"
  "(" [ Expressions ] ")"
````
A ``HashCall`` is used to call the prefix for a copredicate or colemma.
In the non-generic case, just insert `"#[k]"` before the call argument
list where k is the number of recursion levels.

In the case where the `colemma` is generic, the generic type
argument is given before. Here is an example:

```
codatatype Stream<T> = Nil | Cons(head: int, stuff: T, tail: Stream)

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
  // the following shows two equivalent ways to getting essentially the
  // co-inductive hypothesis
  if (*) {
    Theorem0#<T>[_k-1](s);
  } else {
    Theorem0(s);
  }
}

```

where the ``HashCall`` is `"Theorem0#<T>[_k-1](s);"`.
See sections [#sec-copredicates] and [#sec-prefix-lemmas].

## Suffix
````
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

### Augmented Dot Suffix
````
AugmentedDotSuffix_ = ". " DotSuffix [ GenericInstantiation | HashCall ]
````

An augmented dot suffix consists of a simple ``DotSuffix`` optionally
followed by either

* a ``GenericInstantiation`` (for the case where the item
selected by the ``DotSuffix`` is generic), or
* a ``HashCall`` for the case where we want to call a prefix copredicate
  or colemma. The result is the result of calling the prefix copredicate
  or colemma.

### Datatype Update Suffix

````
DatatypeUpdateSuffix_ =
  "." "(" MemberBindingUpdate { "," MemberBindingUpdate } ")"

MemberBindingUpdate =
  ( ident | digits ) ":=" Expression(allowLemma: true, allowLambda: true)
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

```
module NewSyntax {
datatype MyDataType = MyConstructor(myint:int, mybool:bool)
                    | MyOtherConstructor(otherbool:bool)
                    | MyNumericConstructor(42:int)

method test(datum:MyDataType, x:int)
    returns (abc:MyDataType, def:MyDataType, ghi:MyDataType, jkl:MyDataType)
    requires datum.MyConstructor?;
    ensures abc == datum.(myint := x + 2);
    ensures def == datum.(otherbool := !datum.mybool);
    ensures ghi == datum.(myint := 2).(mybool := false);
    // Resolution error: no non_destructor in MyDataType
    //ensures jkl == datum.(non_destructor := 5);
    ensures jkl == datum.(42 := 7);
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



### Subsequence Suffix
````
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

### Slices By Length Suffix
````
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

### Sequence Update Suffix
````
SequenceUpdateSuffix_ =
  "[" Expression(allowLemma: true, allowLambda: true)
      ":=" Expression(allowLemma: true, allowLambda: true)
  "]"
````

For a sequence `s` and expressions `i` and `v`, the expression
`s[i := v]` is the same as the sequence `s` except that at
index `i` it has value `v`.

### Selection Suffix
````
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

### Argument List Suffix
````
ArgumentListSuffix_ = "(" [ Expressions ] ")"
````

An argument list suffix is a parenthesized list of expressions that
are the arguments to pass to a method or function that is being
called. Applying such a suffix causes the method or function
to be called and the result is the result of the call.

## Expression Lists
````
Expressions =
    Expression(allowLemma: true, allowLambda: true)
    { "," Expression(allowLemma: true, allowLambda: true) }
````

The ``Expressions`` non-terminal represents a list of
one or more expressions separated by a comma.

## Compile-Time Constants {#sec-compile-time-constants}

In certain situations in Dafny it is helpful to know what the value of a 
constant is during program analysis, before verification or execution takes
place. For example, a compiler can choose an optimized representation of a 
`newtype` that is a subset of `int` if it knows the range of possible values 
of the subset type: if the range is within 0 to 255 (inclusive), then an 
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
no difference at all to verification, only to the runtime performance of
compiled code. In addition, though, using a symbolic constant (which may 
well be used elsewhere as well) improves the self-documentation of the code.

In Dafny, the following expressions are compile-time constants[^CTC], recursively 
(that is, the arguments of any operation must themselves be compile-time constants):
- int, real, boolean, and string literals
- builtin unary operations: `-` (int and real), `!` (bool and int), and `|...|` (string length)
- binary operations: `+ - * / %` (int and real), `<< >>` (int), `+` (string concatenation), `&& ||` (bool)
- bit operations: `& | ^` (int)
- comparison operations: `< <= > >=` (int and real), `== !=` (int, real, bool, string)
- symbolic values that are declared `const` and have an explicit initialization value that is a compile-time constant
- parenthesized expressions

[^CTC]: This set of operations that are constant-folded may be enlarged in 
future versions of Dafny.
