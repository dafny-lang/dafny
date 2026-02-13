# 9. Expressions {#sec-expressions}

Dafny expressions come in three flavors.
- The bulk of expressions have no side-effects and can be used within
methods, functions, and specifications, and in either compiled or ghost code.
- Some expressions, called [right-hand-side expressions](#sec-rhs-expression),
do have side-effects and may only be used in specific syntactic locations,
such as the right-hand-side of update (assignment) statements; 
object allocation and method calls are two typical examples of [right-hand-side expressions](#sec-rhs-expression). Note that method calls are syntactically
indistinguishable from function calls; both are Expressions ([PrimaryExpressions](#sec-primary-expression)
with an [ArgumentList suffix](#sec-argument-list-suffix)). However, method calls are semantically permitted
only in right-hand-side expression locations.
- Some expressions are allowed only in specifications and other ghost code,
as listed [here](#sec-list-of-specification-expressions).

The grammar of Dafny expressions follows a hierarchy that
reflects the precedence of Dafny operators. The following
table shows the Dafny operators and their precedence
in order of increasing binding power.

 operator                 | precedence | description
--------------------------|:----------:|-----------------------
 `;`                      | 0 | That is [LemmaCall; Expression](#sec-top-level-expression)
--------------------------|------------------------------------
 `<==>`                   | 1 | [equivalence (if and only if)](#sec-equivalence-expression)
--------------------------|------------------------------------
 `==>`                    | 2 | [implication (implies)](#sec-implies-expression)
 `<==`                    | 2 | [reverse implication (follows from)](#sec-implies-expression)
--------------------------|------------------------------------
 `&&`, `&`                | 3 | [conjunction (and)](#sec-logical-expression)
 `||`, `|`                | 3 | [disjunction (or)](#sec-logical-expression)
--------------------------|------------------------------------
 `==`                     | 4 | equality
 `==#[k]`                 | 4 | [prefix equality (coinductive)](#sec-co-equality)
 `!=`                     | 4 | disequality
 `!=#[k]`                 | 4 | [prefix disequality (coinductive)](#sec-co-equality)
 `<`                      | 4 | less than
 `<=`                     | 4 | at most
 `>=`                     | 4 | at least
 `>`                      | 4 | greater than
 `in`                     | 4 | collection membership
 `!in`                    | 4 | collection non-membership
 `!!`                     | 4 | disjointness
--------------------------|------------------------------------
 `<<`                     | 5 | [left-shift](#sec-bit-shift-expression)
 `>>`                     | 5 | [right-shift](#sec-bit-shift-expression)
--------------------------|------------------------------------
 `+`                      | 6 | addition (plus)
 `-`                      | 6 | subtraction (minus)
--------------------------|------------------------------------
 `*`                      | 7 | multiplication (times)
 `/`                      | 7 | division (divided by)
 `%`                      | 7 | modulus (mod)
--------------------------|------------------------------------
 `|`                      | 8 | [bit-wise or](#sec-bitvector-expression)
 `&`                      | 8 | [bit-wise and](#sec-bitvector-expression)
 `^`                      | 8 | [bit-wise exclusive-or (not equal)](#sec-bitvector-expression)
--------------------------|------------------------------------
 `as` operation           | 9 | [type conversion](#sec-as-is-expression)
 `is` operation           | 9 | [type test](#sec-as-is-expression)
--------------------------|------------------------------------
 `-`                      | 10 | arithmetic negation (unary minus)
 `!`                      | 10 | logical negation, bit-wise complement
--------------------------|------------------------------------
 Primary Expressions      | 11 |


## 9.1. Lemma-call expressions ([grammar](#g-top-level-expression)) {#sec-top-level-expression}

Examples:
<!-- %no-check -->
```dafny
var a := L(a,b); a*b
```

This expression has the form `S; E`.
The type of the expression is the type of `E`.
`S` must be a lemma call (though the grammar appears more lenient).
The lemma introduces a fact necessary to establish properties of `E`.

Sometimes an expression will fail unless some relevant fact is known.
In the following example the `F_Fails` function fails to verify
because the `Fact(n)` divisor may be zero. But preceding
the expression by a lemma that ensures that the denominator
is not zero allows function `F_Succeeds` to succeed.
<!-- %check-verify Expressions.1.expect -->
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

One restriction is that a lemma call in this form is permitted only in situations in which the expression itself is not terminated by a semicolon.

A second restriction is that `E` is not always permitted to contain lambda expressions, such 
as in the expressions that are the body of a lambda expression itself, function, method and iterator specifications,
and if and while statements with guarded alternatives.

A third restriction is that `E` is not always permitted to contain a bit-wise or (`|`) operator, 
because it would be ambiguous with the vertical bar used in comprehension expressions.

Note that the effect of the lemma call only extends to the succeeding expression `E` (which may be another `;` expression).

## 9.2. Equivalence Expressions ([grammar](#g-equivalence-expression)) {#sec-equivalence-expression}

Examples:
<!-- %no-check -->
```dafny
A
A <==> B
A <==> C ==> D <==> B 
```

An Equivalence Expression that contains one or more `<==>`s is
a boolean expression and all the operands
must also be boolean expressions. In that case each `<==>`
operator tests for logical equality which is the same as
ordinary equality (but with a different precedence).

See [Section 5.2.1.1](#sec-equivalence-operator) for an explanation of the
`<==>` operator as compared with the `==` operator.

The `<==>` operator is commutative and associative: `A <==> B <==> C` and `(A <==> B) <==> C` and `A <==> (B <==> C)` and `C <==> B <==> A`
are all equivalent and are all true iff an even number of operands are false.

## 9.3. Implies or Explies Expressions ([grammar](#g-implies-expression)) {#sec-implies-expression}

Examples:
<!-- %no-check -->
```dafny
A ==> B
A ==> B ==> C ==> D
B <== A
```

See [Section 5.2.1.3](#sec-implication-and-reverse-implication) for an explanation
of the `==>` and `<==` operators.

## 9.4. Logical Expressions ([grammar](#g-logical-expression)) {#sec-logical-expression}

Examples:
<!-- %no-check -->
```dafny
A && B
A || B
&& A && B && C
```

Note that the Dafny grammar allows a conjunction or disjunction to be
_prefixed_ with `&&` or `||` respectively. This form simply allows a
parallel structure to be written:
<!-- %check-resolve -->
```dafny
method m(x: object?, y:object?, z: object?) {
  var b: bool :=
    && x != null
    && y != null
    && z != null
    ;
}
```
This is purely a syntactic convenience allowing easy edits such as reordering
lines or commenting out lines without having to check that the infix
operators are always where they should be.

Note also that `&&` and `||` cannot be mixed without using parentheses:
`A && B || C` is not permitted. Write `(A && B) || C` or `A && (B || C)` instead.

See [Section 5.2.1.2](#sec-conjunction-and-disjunction) for an explanation
of the `&&` and `||` operators.

## 9.5. Relational Expressions ([grammar](#g-relational-expression)) {#sec-relational-expression}

Examples:
<!-- %no-check -->
```dafny
x == y
x != y
x < y
x >= y
x in y
x ! in y
x !! y
x ==#[k] y
```

The relation expressions compare two or more terms.
As explained in [the section about basic types](#sec-basic-type), `==`, `!=`, ``<``, `>`, `<=`, and `>=`
are _chaining_.

The `in` and `!in` operators apply to collection types as explained in
[Section 5.5](#sec-collection-types) and represent membership or non-membership
respectively.

The `!!` represents disjointness for sets and multisets as explained in
[Section 5.5.1](#sec-sets) and [Section 5.5.2](#sec-multisets).

`x ==#[k] y` is the prefix equality operator that compares
coinductive values for equality to a nesting level of k, as
explained in [the section about co-equality](#sec-co-equality).

## 9.6. Bit Shifts ([grammar](#g-bit-shift-expression)) {#sec-bit-shift-expression}

Examples:
<!-- %no-check -->
```dafny
k << 5
j >> i
```

These operators are the left and right shift operators for bit-vector values.
They take a bit-vector value and an `int`, shifting the bits by the given
amount; the result has the same bit-vector type as the LHS.
For the expression to be well-defined, the RHS value must be in the range 0 to the number of
bits in the bit-vector type, inclusive.

The operations are left-associative: `a << i >> j` is `(a << i) >> j`.

## 9.7. Terms ([grammar](#g-term)) {#sec-addition-expression}

Examples:
<!-- %no-check -->
```dafny
x + y - z
```

`Terms` combine `Factors` by adding or subtracting.
Addition has these meanings for different types:

* arithmetic addition for numeric types ([Section 5.2.2](#sec-numeric-types)])
* union for sets and multisets ([Section 5.5.1](#sec-sets) and [Section 5.5.2](#sec-multisets))
* concatenation for sequences ([Section 5.5.3](#sec-sequences))
* map merging for maps ([Section 5.5.4](#sec-maps))

Subtraction is 

* arithmetic subtraction for numeric types
* set or multiset subtraction for sets and multisets
* domain subtraction for maps.

All addition operations are associative. Arithmetic addition and union are commutative. Subtraction is neither; it groups to the left as expected:
`x - y -z` is `(x - y) -z`.

## 9.8. Factors ([grammar](#g-factor)) {#sec-multiplication-expression}

Examples:
<!-- %no-check -->
```dafny
x * y
x / y
x % y
```

A ``Factor`` combines expressions using multiplication,
division, or modulus. For numeric types these are explained in
[Section 5.2.2](#sec-numeric-types).
As explained there, `/` and `%` on `int` values represent _Euclidean_
integer division and modulus and not the typical C-like programming
language operations.

Only `*` has a non-numeric application. It represents set or multiset
intersection as explained in [Section 5.5.1](#sec-sets) and [Section 5.5.2](#sec-multisets).

`*` is commutative and associative; `/` and `%` are neither but do group to the left.

## 9.9. Bit-vector Operations ([grammar](#g-bit-vector-expression)) {#sec-bitvector-expression}

Examples:
<!-- %no-check -->
```dafny
x | y
x & y
x ^ y
```


These operations take two bit-vector values of the same type, returning
a value of the same type. The operations perform bit-wise _or_ (`|`),
_and_ (`&`), and _exclusive-or_ (`^`). To perform bit-wise equality, use
`^` and `!` (unary complement) together. (`==` is boolean equality of the whole bit-vector.)

These operations are associative and commutative but do not associate with each other.
Use parentheses: `a & b | c` is illegal; use `(a & b) | c` or `a & (b | c)`
instead.

Bit-vector operations are not allowed in some contexts.
The `|` symbol is used both for bit-wise or and as the delimiter in a
[cardinality](#sec-cardinality-expression) expression: an ambiguity arises if
the expression E in `| E |` contains a `|`. This situation is easily
remedied: just enclose E in parentheses, as in `|(E)|`.
The only type-correct way this can happen is if the expression is
a comprehension, as in `| set x: int :: x | 0x101 |`.

## 9.10. As (Conversion) and Is (type test) Expressions ([grammar](#g-as-is-expression)) {#sec-as-is-expression}

Examples:
<!-- %no-check -->
```dafny
e as MyClass
i as bv8
e is MyClass
```

The `as` expression converts the given LHS to the type stated on the RHS,
with the result being of the given type. The following combinations
of conversions are permitted:

* Any type to itself
* Any int-based or real-based numeric type or bit-vector type to another int-based or real-based numeric type or bit-vector type
* Any base type to a subset or newtype with that base
* Any subset or newtype to its base type or a subset or newtype of the same base
* Any type to a subset or newtype that has the type as its base
* Any trait to a class or trait that extends (perhaps recursively) that trait
* Any class or trait to a trait extended by that class or trait

Some of the conversions above are already implicitly allowed, without the
`as` operation, such as from a subset type to its base. In any case, it
must be able to be proved that the value of the given expression is a
legal value of the given type. For example, `5 as MyType` is permitted (by the verifier) only if `5` is a legitimate value of`MyType` (which must be a numeric type).

The `as` operation is like a grammatical suffix or postfix operation.
However, note that the unary operations bind more tightly than does `as`.
That is `- 5 as nat` is `(- 5) as nat` (which fails), whereas `a * b as nat`
is `a * (b as nat)`. On the other hand, `- a[4]` is `- (a[4])`.

The `is` expression is grammatically similar to the `as` expression, with the
same binding power. The `is` expression is a type test that
returns a `bool` value indicating whether the LHS expression is a legal
value of the RHS type. The expression can be used to check
whether a trait value is of a particular class type. That is, the expression
in effect checks the allocated type of a trait.

The RHS type of an `is` expression can always be a supertype of the type of the LHS
expression, in which case the result is trivally true. 
Other than that, the RHS must be based on a reference type and the
LHS expression must be assignable to the RHS type. Furthermore, in order to be
compilable, the RHS type must not be a subset type other than a non-null reference
type, and the type parameters of the RHS must be uniquely determined from the
type parameters of the LHS type. The last restriction is designed to make it
possible to perform type tests without inspecting type parameters at run time.
For example, consider the following types:

<!-- %check-resolve -->
```dafny
trait A { }
trait B<X> { }
class C<Y> extends B<Y> { }
class D<Y(==)> extends B<set<Y>> { }
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

## 9.11. Unary Expressions ([grammar](#g-unary-expression)) {#sec-unary-expression}

Examples:
<!-- %no-check -->
```dafny
-x
- - x
! x
```

A unary expression applies 

- logical complement (`!` -- [Section 5.2.1](#sec-booleans)),
- bit-wise complement (`!` -- [Section 5.2.4](#sec-bit-vector-types)),
- numeric negation (`-` -- [Section 5.2.2](#sec-numeric-types)), or
- bit-vector negation (`-` -- [Section 5.2.4](#sec-bit-vector-types))

to its operand.

## 9.12. Primary Expressions ([grammar](#g-primary-expression)) {#sec-primary-expression}

Examples:
<!-- %no-check -->
```dafny
true
34
M(i,j)
b.c.d
[1,2,3]
{2,3,4}
map[1 => 2, 3 => 4]
(i:int,j:int)=>i+j
if b then 4 else 5
```

After descending through all the binary and unary operators we arrive at
the primary expressions, which are explained in subsequent sections. 
A number of these can be followed by 0 or more suffixes
to select a component of the value.

## 9.13. Lambda expressions ([grammar](#g-lambda-expression)) {#sec-lambda-expression}

Examples:
<!-- %no-check -->
```dafny
x => -x
_ => true
(x,y) => x*y
(x:int, b:bool) => if b then x else -x
x requires x > 0 => x-1
```

See [Section 7.4](#sec-lambda-specification) for a description of specifications for lambda expressions.

In addition to named functions, Dafny supports expressions that define
functions.  These are called _lambda (expression)s_ (some languages
know them as _anonymous functions_).  A lambda expression has the
form:
<!-- %no-check -->
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
<!-- %no-check -->
```dafny
x => x + 1
```

The _specification_ is a list of clauses `requires E` or
`reads W`, where `E` is a boolean expression and `W` is a frame
expression.

_body_ is an expression that defines the function's return
value.  The body must be [well-formed](#sec-assertion-batches) for all possible values of the
parameters that satisfy the precondition (just like the bodies of
named functions and methods).  In some cases, this means it is
necessary to write explicit `requires` and `reads` clauses.  For
example, the lambda expression
<!-- %no-check -->
```dafny
x requires x != 0 => 100 / x
```
would not be [well-formed](#sec-assertion-batches) if the `requires` clause were omitted,
because of the possibility of division-by-zero.

In settings where functions cannot be partial and there are no
restrictions on reading the heap, the _eta expansion_ of a function
`F: T -> U` (that is, the wrapping of `F` inside a lambda expression
in such a way that the lambda expression is equivalent to `F`) would
be written `x => F(x)`.  In Dafny, eta expansion must also account for
the precondition and reads set of the function, so the eta expansion
of `F` looks like:
<!-- %no-check -->
```dafny
x requires F.requires(x) reads F.reads(x) => F(x)
```

## 9.14. Left-Hand-Side Expressions ([grammar](#g-lhs-expression)) {#sec-lhs-expression}

Examples:
<!-- %no-check -->
```dafny
x
a[k]
LibraryModule.F().x
old(o.f).x
```

A left-hand-side expression is only used on the left hand
side of an [Update statement](#sec-update-and-call-statement)
or an [Update with Failure Statement](#sec-update-with-failure-statement).

An LHS can be

- a simple identifier: `k`
- an expression with a dot suffix: `this.x`, `f(k).y`
- an expression with an array selection: `a[k]`, `f(a8)[6]`

## 9.15. Right-Hand-Side Expressions ([grammar](#g-rhs-expression)) {#sec-rhs-expression}

Examples: 
<!-- %no-check -->
```dafny
new int[6]
new MyClass
new MyClass(x,y,z)
x+y+z
*
```

A Right-Hand-Side expression is an expression-like construct that may have 
side-effects. Consequently such expressions
 can only be used within certain statements
within methods, and not as general expressions or within functions or specifications.

An RHS is either an array allocation, an object allocation,
a havoc right-hand-side, a method call, or a simple expression, optionally followed
by one or more attributes.

Right-hand-side expressions (that are not just regular expressions) appear in the following constructs:

- [return statements](#sec-return-statement),
- [yield statements](#sec-yield-statement),
- [update statements](#sec-update-and-call-statement),
- [update-with-failure statements](#sec-update-with-failure-statement), or
- [variable declaration statements](#sec-variable-declaration-statement).

These are the only contexts in which arrays or objects may be
allocated or in which havoc may be stipulated.

## 9.16. Array Allocation ([grammar](#g-array-allocation-expression)) {#sec-array-allocation}

Examples:
<!-- %no-check -->
```dafny
new int[5,6]
new int[5][2,3,5,7,11]
new int[][2,3,5,7,11]
new int[5](i => i*i)
new int[2,3]((i,j) => i*j)
```

This right-hand-side expression allocates a new single or multi-dimensional array (cf. [Section 5.10](#sec-array-type)).
The initialization portion is optional. One form is an
explicit list of values, in which case the dimension is optional:
<!-- %no-check -->
```dafny
var a := new int[5];
var b := new int[5][2,3,5,7,11];
var c := new int[][2,3,5,7,11];
var d := new int[3][4,5,6,7]; // error
```
The comprehension form requires a dimension and uses a function of
type `nat -> T` where `T` is the array element type:
<!-- %no-check -->
```dafny
var a := new int[5](i => i*i);
```

To allocate a multi-dimensional array, simply give the sizes of
each dimension. For example,
<!-- %no-check -->
```dafny
var m := new real[640, 480];
```
allocates a 640-by-480 two-dimensional array of `real`s. The initialization
portion cannot give a display of elements like in the one-dimensional
case, but it can use an initialization function. A function used to initialize
a n-dimensional array requires a function from n `nat`s to a `T`, where `T`
is the element type of the array. Here is an example:
<!-- %no-check -->
```dafny
var diag := new int[30, 30]((i, j) => if i == j then 1 else 0);
```

Array allocation is permitted in ghost contexts. If any expression
used to specify a dimension or initialization value is ghost, then the
`new` allocation can only be used in ghost contexts. Because the
elements of an array are non-ghost, an array allocated in a ghost
context in effect cannot be changed after initialization.

## 9.17. Object Allocation ([grammar](#g-object-allocation-expression)) {#sec-object-allocation}

Examples:
<!-- %no-check -->
```dafny
new MyClass
new MyClass.Init
new MyClass.Init(1,2,3)
```

This right-hand-side expression 
allocates a new object of a class type as explained
in section [Class Types](#sec-class-types).

## 9.18. Havoc Right-Hand-Side ([grammar](#g-havoc-expression)) {#sec-havoc-expression}

Examples:
<!-- %no-check -->
```dafny
*
```
A havoc right-hand-side is just a `*` character.
It produces an arbitrary value of its associated
type. The "assign-such-that"
operator (`:|`) can be used to obtain a more constrained arbitrary value. 
See [Section 8.5](#sec-update-and-call-statement).

## 9.19. Constant Or Atomic Expressions ([grammar](#g-atomic-expression)) {#sec-atomic-expression}

Examples:
<!-- %no-check -->
```dafny
this
null
5
5.5
true
'a'
"dafny"
( e )
| s |
old(x)
allocated(x)
unchanged(x)
fresh(e)
assigned(x)
```

These expressions are never l-values. They include

- [literal expressions](#sec-literal-expression)
- [parenthesized expressions](#sec-parenthesized-expression)
- [`this` expressions](#sec-this-expression)
- [fresh expressions](#sec-fresh-expression)
- [allocated expressions](#sec-allocated-expression)
- [unchanged expressions](#sec-unchanged-expression)
- [old expressions](#sec-old-expression)
- [cardinality expressions](#sec-cardinality-expression)
- [assigned expressions](#sec-assigned-expression)

## 9.20. Literal Expressions ([grammar](#g-literal-expression)} {#sec-literal-expression}

Examples:
<!-- %no-check -->
```dafny
5
5.5
true
'a'
"dafny"
```

A literal expression is a null object reference or a boolean,
integer, real, character or string literal.

## 9.21. `this` Expression ([grammar](#g-this-expression)) {#sec-this-expression}

Examples:
<!-- %no-check -->
```dafny
this
```

The `this` token denotes the current object in the context of 
a constructor, instance method, or instance function.


## 9.22. Old and Old@ Expressions ([grammar](#g-old-expression)) {#sec-old-expression}

Examples:
<!-- %no-check -->
```dafny
old(c)
old@L(c)
```

An _old expression_ is used in postconditions or in the body of a method
or in the body or specification of any two-state function or two-state lemma;
an _old_ expression with a label is used only in the body of a method at a point
where the label dominates its use in the expression.

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
If the argument of `old` is a local variable or out-parameter. Dafny issues a warning.

[^Old]: The semantics of `old` in Dafny differs from similar constructs in other specification languages like ACSL or JML.

The argument of an `old` expression may not contain nested `old`,
[`fresh`](#sec-fresh-expression),
or [`unchanged`](#sec-unchanged-expression) expressions,
nor [two-state functions](#sec-two-state) or [two-state lemmas](#sec-two-state-lemma).

Here are some explanatory examples. All `assert` statements verify to be true.
<!-- %check-verify-warn Expressions.2.expect -->
```dafny
class A {

  var value: int

  method m(i: int)
    requires i == 6
    requires value == 42
    modifies this
  {
    var j: int := 17;
    value := 43;
    label L:
    j := 18;
    value := 44;
    label M:
    assert old(i) == 6; // i is local, but can't be changed anyway
    assert old(j) == 18; // j is local and not affected by old
    assert old@L(j) == 18; // j is local and not affected by old
    assert old(value) == 42;
    assert old@L(value) == 43;
    assert old@M(value) == 44 && this.value == 44;
    // value is this.value; 'this' is the same
    // same reference in current and pre state but the
    // values stored in the heap as its fields are different;
    // '.value' evaluates to 42 in the pre-state, 43 at L,
    // and 44 in the current state
  }
}
```
<!-- %check-verify -->
```dafny
class A {
  var value: int
  constructor ()
     ensures value == 10
  {
     value := 10;
  }
}

class B {
   var a: A
   constructor () { a := new A(); }

   method m()
     requires a.value == 11
     modifies this, this.a
   {
     label L:
     a.value := 12;
     label M:
     a := new A(); // Line X
     label N:
     a.value := 20;
     label P:

     assert old(a.value) == 11;
     assert old(a).value == 12; // this.a is from pre-state,
                                // but .value in current state
     assert old@L(a.value) == 11;
     assert old@L(a).value == 12; // same as above
     assert old@M(a.value) == 12; // .value in M state is 12
     assert old@M(a).value == 12;
     assert old@N(a.value) == 10; // this.a in N is the heap
                                  // reference at Line X
     assert old@N(a).value == 20; // .value in current state is 20
     assert old@P(a.value) == 20;
     assert old@P(a).value == 20;
  }
}
```
<!-- %check-verify -->
```dafny
class A {
  var value: int
  constructor ()
     ensures value == 10
  {
     value := 10;
  }
}

class B {
   var a: A
   constructor () { a := new A(); }

   method m()
     requires a.value == 11
     modifies this, this.a
   {
     label L:
     a.value := 12;
     label M:
     a := new A(); // Line X
     label N:
     a.value := 20;
     label P:

     assert old(a.value) == 11;
     assert old(a).value == 12; // this.a is from pre-state,
                                // but .value in current state
     assert old@L(a.value) == 11;
     assert old@L(a).value == 12; // same as above
     assert old@M(a.value) == 12; // .value in M state is 12
     assert old@M(a).value == 12;
     assert old@N(a.value) == 10; // this.a in N is the heap
                                  // reference at Line X
     assert old@N(a).value == 20; // .value in current state is 20
     assert old@P(a.value) == 20;
     assert old@P(a).value == 20;
  }
}
```
The next example demonstrates the interaction between `old` and array elements.
<!-- %check-verify-warn Expressions.3.expect -->
```dafny
class A {
  var z1: array<nat>
  var z2: array<nat>

  method mm()
    requires z1.Length > 10 && z1[0] == 7
    requires z2.Length > 10 && z2[0] == 17
    modifies z2
  {
    var a: array<nat> := z1;
    assert a[0] == 7;
    a := z2;
    assert a[0] == 17;
    assert old(a[0]) == 17; // a is local with value z2
    z2[0] := 27;
    assert old(a[0]) == 17; // a is local, with current value of
                            // z2; in pre-state z2[0] == 17
    assert old(a)[0] == 27; // a is local, so old(a) has no effect
  }
}
```
## 9.23. Fresh Expressions ([grammar](#g-fresh-expression)) {#sec-fresh-expression}

Examples:
<!-- %no-check -->
```dafny
fresh(e)
fresh@L(e)
```

`fresh(e)` returns a boolean value that is true if
the objects denoted by expression `e` were all
freshly allocated since the time of entry to the enclosing method,
or since [`label L:`](#sec-labeled-statement) in the variant `fresh@L(e)`.
The argument is an object or set of objects.
For example, consider this valid program:

<!-- %check-verify -->
```dafny
class C { constructor() {} }
method f(c1: C) returns (r: C)
  ensures fresh(r)
{
  assert !fresh(c1);
  var c2 := new C();
  label AfterC2:
  var c3 := new C();
  assert fresh(c2) && fresh(c3);
  assert fresh({c2, c3});
  assert !fresh@AfterC2(c2) && fresh@AfterC2(c3);
  r := c2;
}
```

The `L` in the variant `fresh@L(e)` must denote a [label](#sec-labeled-statement) that, in the
enclosing method's control flow, [dominates the expression](#sec-labeled-statement). In this
case, `fresh@L(e)` returns `true` if the objects denoted by `e` were all
freshly allocated since control flow reached label `L`.

The argument of `fresh` must be either an [`object`](#sec-object-type) reference
or a set or sequence of object references.
In this case, `fresh(e)` (respectively `fresh@L(e)` with a label)
is a synonym of [`old(!allocated(e))`](#sec-allocated-expression)
(respectively [`old@L(!allocated(e))`](#sec-allocated-expression))


## 9.24. Allocated Expressions ([grammar](#g-allocated-expression)) {#sec-allocated-expression}

Examples:
<!-- %no-check -->
```dafny
allocated(c)
allocated({c1,c2})
```

For any expression `e`, the expression `allocated(e)` evaluates to `true`
in a state if the value of `e` is available in that state, meaning that
it could in principle have been the value of a variable in that state.

For example, consider this valid program:

<!-- %check-verify -->
```dafny
class C { constructor() {} }
datatype D = Nil | Cons(C, D)
method f() {
  var d1, d2 := Nil, Nil;
  var c1 := new C();
  label L1:
  var c2 := new C();
  label L2:
  assert old(allocated(d1) && allocated(d2));
  d1 := Cons(c1, Nil);
  assert old(!allocated(d1) && allocated(d2));
  d2 := Cons(c2, Nil);
  assert old(!allocated(d1) && !allocated(d2));
  assert allocated(d1) && allocated(d2);
  assert old@L1(allocated(d1) && !allocated(d2));
  assert old@L2(allocated(d1) && allocated(d2));
  d1 := Nil;
  assert old(allocated(d1) && !allocated(d2));
}
```

This can be useful when, for example, `allocated(e)` is evaluated in an
[`old`](#sec-old-expression) state. Like in the example, where `d1` is a local variable holding a datatype value
`Cons(c1, Nil)` where `c1` is an object that was allocated in the enclosing
method, then [`old(allocated(d))`](#sec-old-expression) is `false`.

If the expression `e` is of a reference type, then `!old(allocated(e))`
is the same as [`fresh(e)`](#sec-fresh-expression).


## 9.25. Unchanged Expressions ([grammar](#g-unchanged-expression)) {#sec-unchanged-expression}

Examples:
<!-- %no-check -->
```dafny
unchanged(c)
unchanged([c1,c2])
unchanged@L(c)
```

The `unchanged` expression returns `true` if and only if every reference
denoted by its arguments has the same value for all its fields in the
old and current state. For example, if `c` is an object with two
fields, `x` and `y`, then `unchanged(c)` is equivalent to
<!-- %no-check -->
```dafny
c.x == old(c.x) && c.y == old(c.y)
```

Each argument to `unchanged` can be a reference, a set of references, or
a sequence of references, each optionally followed by a back-tick and field name. 
This form with a frame field expresses that just the field `f`,
not necessarily all fields, has the same value in the old and current
state.
If there is such a frame field, all the references must have the same type,
which must have a field of that name.

The optional `@`-label says to use the state at that label as the old-state instead of using
the `old` state (the pre-state of the method). That is, using the example `c` from above, the expression
`unchanged@Lbl(c)` is equivalent to
<!-- %no-check -->
```dafny
c.x == old@Lbl(c.x) && c.y == old@Lbl(c.y)
```

Each reference denoted by the arguments of `unchanged` must be non-null and
must be allocated in the old-state of the expression.


## 9.26. Cardinality Expressions ([grammar](#g-cardinality-expression)) {#sec-cardinality-expression}

Examples:
<!-- %no-check -->
```dafny
|s|
|s[1..i]|
```

For a finite-collection expression `c`, `|c|` is the cardinality of `c`. For a
finite set or sequence, the cardinality is the number of elements. For
a multiset, the cardinality is the sum of the multiplicities of the
elements. For a finite map, the cardinality is the cardinality of the
domain of the map. Cardinality is not defined for infinite sets or infinite maps.
For more information, see [Section 5.5](#sec-collection-types).

## 9.27. Parenthesized Expressions ([grammar](#g-parenthesized-expression)) {#sec-parenthesized-expression}

A parenthesized expression is a list of zero or more expressions
enclosed in parentheses.

If there is exactly one expression enclosed then the value is just
the value of that expression.

If there are zero or more than one, the result is a `tuple` value.
See [Section 5.13](#sec-tuple-types).

## 9.28. Sequence Display Expression ([grammar](#g-sequence-display-expression)) {#sec-seq-comprehension}

Examples:
<!-- %no-check -->
```dafny
[1, 2, 3]
[1]
[]
seq(k, n => n+1)
```

A sequence display expression provides a way to construct
a sequence with given values. For example

<!-- %no-check -->
```dafny
[1, 2, 3]
```
is a sequence with three elements in it.

<!-- %no-check -->
```dafny
seq(k, n => n+1)
```
is a sequence of k elements whose values are obtained by evaluating the
second argument (a function, in this case a lambda expression) on the indices 0 up to k.

See [this section](#sec-sequences) for more information on
sequences.

## 9.29. Set Display Expression ([grammar](#g-set-display-expression)) {#sec-set-display-expression}

Examples:
<!-- %no-check -->
```dafny
{}
{1,2,3}
iset{1,2,3,4}
multiset{1,2,2,3,3,3}
multiset(s)
```

A set display expression provides a way of constructing a set with given
elements. If the keyword `iset` is present, then a potentially infinite
set (with the finite set of given elements) is constructed.

For example

<!-- %no-check -->
```dafny
{1, 2, 3}
```
is a set with three elements in it.
See [Section 5.5.1](#sec-sets) for more information on
sets.

A multiset display expression provides a way of constructing
a multiset with given elements and multiplicities. For example

<!-- %no-check -->
```dafny
multiset{1, 1, 2, 3}
```
is a multiset with three elements in it. The number 1 has a multiplicity of 2,
and the numbers 2 and 3 each have a multiplicity of 1.

A multiset cast expression converts a set or a sequence
into a multiset as shown here:

<!-- %no-check -->
```dafny
var s : set<int> := {1, 2, 3};
var ms : multiset<int> := multiset(s);
ms := ms + multiset{1};
var sq : seq<int> := [1, 1, 2, 3];
var ms2 : multiset<int> := multiset(sq);
assert ms == ms2;
```

Note that `multiset{1, 1}` is a multiset holding the value `1` with multiplicity 2,
but in `multiset({1,1})` the multiplicity is 1, because the expression `{1,1}` is the set `{1}`,
which is then converted to a multiset.

See [Section 5.5.2](#sec-multisets) for more information on multisets.

## 9.30. Map Display Expression ([grammar](#g-map-display-expression)) {#sec-map-display-expression}

Examples:
<!-- %no-check -->
```dafny
map[]
map[1 := "a", 2 := "b"]
imap[1 := "a", 2 := "b"]
```

A map display expression builds a finite or potentially infinite
map from explicit mappings. For example:

<!-- %check-resolve -->
```dafny
const m := map[1 := "a", 2 := "b"]
ghost const im := imap[1 := "a", 2 := "b"]
```

See [Section 5.5.4](#sec-maps) for more details on maps and imaps.

## 9.31. Endless Expression ([grammar](#g-endless-expression)) {#sec-endless-expression}

_Endless expression_ gets it name from the fact that all its alternate
productions have no terminating symbol to end them, but rather they
all end with an arbitrary expression at the end. The various
endless expression alternatives are described in the following subsections.

### 9.31.1. If Expression ([grammar](#g-if-expression)) {#sec-if-expression}

Examples:
<!-- %no-check -->
```dafny
if c then e1 else e2
if x: int :| P(x) then x else 0
```


An _if expression_ is a conditional (ternary) expression. It first evaluates
the condition expression that follows the `if`. If the condition evaluates to `true` then
the expression following the `then` is evaluated and its value is the
result of the expression. If the condition evaluates to `false` then the
expression following the `else` is evaluated and that value is the result
of the expression. It is important that only the selected expression
is evaluated as the following example shows.

<!-- %no-check -->
```dafny
var k := 10 / x; // error, may divide by 0.
var m := if x != 0 then 10 / x else 1; // ok, guarded
```

The `if` expression also permits a binding form.
In this case the condition of the `if` is an existential asking
"does there exist a value satisfying the given predicate?".
If not, the else branch is evaluated. But if so, then an
(arbitrary) value that does satisfy the given predicate is
bound to the given variable and that variable is in scope in 
the then-branch of the expression.

For example, in the code
<!-- %check-verify -->
```dafny
predicate P(x: int) {
  x == 5 || x == -5
}
method main() {
  assert P(5);
  var y := if x: int :| P(x) then x else 0;
  assert y == 5 || y == -5;
}
```
`x` is given some value that satisfies `P(x)`, namely either `5` or `-5`.
That value of `x` is the value of the expression in the `then` branch above; if there is no value satisfying `P(x)`,
then `0` is returned. Note that if `x` is declared to be a `nat` in this example, then only
the value `5` would be permissible.

This binding form of the `if` expression acts in the same way as the binding form of the [`if` statement](#sec-if-statement).

In the example given, the binder for `x` has no constraining range, so the expression is `ghost`;
if a range is given, such as `var y := if x: int :| 0 <= x < 10 && P(x) then x else 0;`,
then the `if` and `y` are no longer ghost, and `y` could be used, for example, in a `print` statement.

### 9.31.2. Case and Extended Patterns ([grammar](#g-pattern)) {#sec-case-pattern}

Patterns are used for (possibly nested)
pattern matching on inductive, coinductive or base type values.
They are used in 
[match statements](#sec-match-statement),
[match expressions](#sec-match-expression),
[let expressions](#sec-let-expression),
and [variable declarations](#sec-variable-declaration-statement).
The match expressions and statements allow literals,
symbolic constants, and disjunctive (“or”) patterns.

When matching an inductive or coinductive value in
a match statement or expression, the pattern
must correspond to one of the following:

* (0) a case disjunction (“or-pattern”)
* (1) bound variable (a simple identifier),
* (2) a constructor of the type of the value,
* (3) a literal of the correct type, or
* (4) a symbolic constant.

If the extended pattern is

* a sequence of `|`-separated sub-patterns, then the pattern matches values
  matched by any of the sub-patterns.
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

Disjunctive patterns may not bind variables, and may not be nested inside other
patterns.

Any patterns inside the parentheses of a constructor (or tuple) pattern are then
matched against the arguments that were given to the
constructor when the value was constructed.
The number of patterns must match the number
of parameters to the constructor (or the arity of the
tuple).

When matching a value of base type, the pattern should
either be a literal expression of the same type as the value,
or a single identifier matching all values of this type.

Patterns may be nested. The  bound variable
identifiers contained in all the patterns must be distinct.
They are bound to the corresponding values in the value being
matched. (Thus, for example, one cannot repeat a bound variable to
attempt to match a constructor that has two identical arguments.)

### 9.31.3. Match Expression ([grammar](#g-match-expression)) {#sec-match-expression}

A _match expression_ is used to conditionally evaluate and select an
expression depending on the value of an algebraic type, i.e. an inductive
type, a coinductive type, or a base type.

All of the variables in the patterns must be distinct.
If types for the identifiers are not given then types are inferred
from the types of the constructor's parameters. If types are
given then they must agree with the types of the
corresponding parameters.

The expression following the `match` keyword is called the
_selector_. A match expression is evaluated by first evaluating the selector.
The patterns of each match alternative are then compared, in order,
 with the resulting value until a matching pattern is found, as described in
the [section on case bindings](#sec-case-pattern).
If the constructor had
parameters, then the actual values used to construct the selector
value are bound to the identifiers in the identifier list.
The expression to the right of the `=>` in the matched alternative is then
evaluated in the environment enriched by this binding. The result
of that evaluation is the result of the match expression.

Note that the braces enclosing the sequence of match alternatives may be omitted.
Those braces are required if lemma or lambda expressions are used in the
body of any match alternative; they may also be needed for disambiguation if
there are nested match expressions.

### 9.31.4. Quantifier Expression ([grammar](#g-quantifier-expression)) {#sec-quantifier-expression}

Examples:
<!-- %no-check -->
```dafny
forall x: int :: x > 0
forall x: nat | x < 10 :: x*x < 100
exists x: int :: x * x == 25
```

A _quantifier expression_ is a boolean expression that specifies that a
given expression (the one following the `::`) is true for all (for
**forall**) or some (for **exists**) combination of values of the
quantified variables, namely those in the given quantifier domain.
See [Section 2.7.4](#sec-quantifier-domains) for more details on quantifier domains.

Here are some examples:
<!-- %no-check -->
```dafny
assert forall x : nat | x <= 5 :: x * x <= 25;
(forall n :: 2 <= n ==> (exists d :: n < d < 2*n))
assert forall x: nat | 0 <= x < |s|, y <- s[x] :: y < x;
```

The quantifier identifiers are _bound_ within the scope of the
expressions in the quantifier expression.

If types are not given for the quantified identifiers, then Dafny
attempts to infer their types from the context of the expressions.
It this is not possible, the program is in error.


### 9.31.5. Set Comprehension Expressions ([grammar](#g-set-comprehension-expression)) {#sec-set-comprehension-expression}

Examples:
<!-- %check-resolve -->
```dafny
const c1 := set x: nat | x < 100
const c2 := set x: nat | x < 100 :: x * x
const c3 := set x: nat, y: nat | x < y < 100 :: x * y
ghost const c4 := iset x: nat | x > 100
ghost const c5: iset<int> := iset s
const c6 := set x <- c3 :: x + 1
```

A set comprehension expression is an expression that yields a set
(possibly infinite only if `iset` is used) that
satisfies specified conditions. There are two basic forms.

If there is only one quantified variable, the optional ``"::" Expression``
need not be supplied, in which case it is as if it had been supplied
and the expression consists solely of the quantified variable.
That is,

<!-- %no-check -->
```dafny
set x : T | P(x)
```

is equivalent to

<!-- %no-check -->
```dafny
set x : T | P(x) :: x
```

For the full form

<!-- %no-check -->
```dafny
var S := set x1: T1 <- C1 | P1(x1),
             x2: T2 <- C2 | P2(x1, x2),
             ... 
             :: Q(x1, x2, ...)
```

the elements of `S` will be all values resulting from evaluation of `Q(x1, x2, ...)`
for all combinations of quantified variables `x1, x2, ...` (from their respective `C1, C2, ...`
domains) such that all predicates `P1(x1), P2(x1, x2), ...` hold. 

For example,

<!-- %no-check -->
```dafny
var S := set x:nat, y:nat | x < y < 3 :: (x, y)
```
yields `S == {(0, 1), (0, 2), (1, 2) }`

The types on the quantified variables are optional and if not given Dafny
will attempt to infer them from the contexts in which they are used in the
various expressions. The `<- C` domain expressions are also optional and default to
`iset x: T` (i.e. all values of the variable's type), as are the `| P` expressions which
default to `true`. See also [Section 2.7.4](#sec-quantifier-domains) for more details on quantifier domains.

If a finite set was specified ("set" keyword used), Dafny must be able to prove that the
result is finite otherwise the set comprehension expression will not be
accepted.

Set comprehensions involving reference types such as

<!-- %no-check -->
```dafny
set o: object
```

are allowed in ghost expressions within methods, but not in ghost functions[^set-of-objects-not-in-functions].
In particular, in ghost contexts, the
check that the result is finite should allow any set comprehension
where the bound variable is of a reference type. In non-ghost contexts,
it is not allowed, because--even though the resulting set would be
finite--it is not pleasant or practical to compute at run time.

[^set-of-objects-not-in-functions]: In order to be deterministic, the result of a function should only depend on the arguments and of the objects  it [reads](#sec-reads-clause), and Dafny does not provide a way to explicitly pass the entire heap as the argument to a function. See [this post](https://github.com/dafny-lang/dafny/issues/1366) for more insights.

The universe in which set comprehensions are evaluated is the set of all
_allocated_ objects, of the appropriate type and satisfying the given predicate.
For example, given

<!-- %check-resolve -->
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

### 9.31.6. Statements in an Expression ([grammar](#g-statement-in-expression)) {#sec-statement-in-an-expression}

Examples:
<!-- %no-check -->
```dafny
assert x != 0; 10/x
assert x != 0; assert y > 0; y/x
assume x != 0; 10/x
expect x != 0; 10/x
reveal M.f; M.f(x)
calc { x * 0; == 0; } x/1;
```

A ``StmtInExpr`` is a kind of statement that is allowed to
precede an expression in order to ensure that the expression
can be evaluated without error. For example:

<!-- %no-check -->
```dafny
assume x != 0; 10/x
```

`Assert`, `assume`, `expect`, `reveal` and `calc` statements can be used in this way.

### 9.31.7. Let and Let or Fail Expression ([grammar](#g-let-expression)) {#sec-let-expression}

Examples:
<!-- %no-check -->
```dafny
var x := f(y); x*x
var x :- f(y); x*x
var x :| P(x); x*x
var (x, y) := T(); x + y   // T returns a tuple
var R(x,y) := T(); x + y   // T returns a datatype value R
```


A `let` expression allows binding of intermediate values to identifiers
for use in an expression. The start of the `let` expression is
signaled by the `var` keyword. They look much like a local variable
declaration except the scope of the variable only extends to the
enclosed expression.

For example:
<!-- %no-check -->
```dafny
var sum := x + y; sum * sum
```

In the simple case, the pattern is just an identifier with optional
type (which if missing is inferred from the rhs).

The more complex case allows destructuring of constructor expressions.
For example:

<!-- %check-resolve -->
```dafny
datatype Stuff = SCons(x: int, y: int) | Other
function GhostF(z: Stuff): int
  requires z.SCons?
{
  var SCons(u, v) := z; var sum := u + v; sum * sum
}
```

The Let expression has a failure variant
that simply uses `:-` instead of `:=`. This Let-or-Fail expression also permits propagating
failure results. However, in statements ([Section 8.6](#sec-update-with-failure-statement)), failure results in
immediate return from the method; expressions do not have side effects or immediate return
mechanisms. Rather, if the expression to the right of `:-` results in a failure value `V`,
the overall expression returns `V.PropagateFailure()`; if there is no failure, the expression following the 
semicolon is returned. Note that these two possible return values must have the same type (or be 
implicitly convertible to the same type). Typically that means that `tmp.PropagateFailure()` is a failure value and
`E` is a value-carrying success value, both of the same failure-compatible type, 
as described in [Section 8.6](#sec-update-with-failure-statement).

The expression `:- V; E` is desugared into the _expression_
<!-- %no-check -->
```dafny
var tmp := V;
if tmp.IsFailure()
then tmp.PropagateFailure()
else E
```

The expression `var v :- V; E` is desugared into the _expression_
<!-- %no-check -->
```dafny
var tmp := V;
if tmp.IsFailure()
then tmp.PropagateFailure()
else var v := tmp.Extract(); E
```

If the RHS is a list of expressions then the desugaring is similar. `var v, v1 :- V, V1; E` becomes
<!-- %no-check -->
```dafny
var tmp := V;
if tmp.IsFailure()
then tmp.PropagateFailure()
else var v, v1 := tmp.Extract(), V1; E
```

So, if tmp is a failure value, then a corresponding failure value is propagated along; otherwise, the expression
is evaluated as normal.

### 9.31.8. Map Comprehension Expression ([grammar](#g-map-comprehension-expression)) {#sec-map-comprehension-expression}

Examples:
<!-- %no-check -->
```dafny
map x : int | 0 <= x <= 10 :: x * x;
map x : int | 0 <= x <= 10 :: -x := x * x;
imap x : int | 10 < x :: x * x;
```

A _map comprehension expression_  defines a finite or infinite map value
by defining a domain and for each value in the domain,
giving the mapped value using the expression following the "::".
See [Section 2.7.4](#sec-quantifier-domains) for more details on quantifier domains.

For example:
<!-- %check-resolve -->
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
But imaps may be infinite as the examples show. The last example shows
creation of an infinite map that gives the same results as a function.

If the expression includes the `:=` token, that token separates
domain values from range values. For example, in the following code
<!-- %check-resolve -->
```dafny
method test()
{
  var m := map x : int | 1 <= x <= 10 :: 2*x := 3*x;
}
```
`m` maps `2` to `3`, `4` to `6`, and so on.

## 9.32. Name Segment ([grammar](#g-name-segment)) {#sec-name-segment}

Examples:
<!-- %no-check -->
```dafny
I
I<int,C>
I#[k]
I#<int>[k]
```

A _name segment_ names a Dafny entity by giving its declared
name optionally followed by information to
make the name more complete. For the simple case, it is
just an identifier. Note that a name segment may be followed
by [suffixes](#sec-suffix), including the common '.' and further name segments.

If the identifier is for a generic entity, it is followed by
a ``GenericInstantiation`` which provides actual types for
the type parameters.

To reference a prefix predicate (see [Section 5.14.3.5](#sec-copredicates)) or
prefix lemma (see [Section 5.14.3.6.3](#sec-prefix-lemmas)), the identifier
must be the name of the greatest predicate or greatest lemma and it must be
followed by a [_hash call_](#sec-hash-call).

## 9.33. Hash call ([grammar](#g-hash-call)) {#sec-hash-call}

A _hash call_  is used to call the prefix for a greatest predicate or greatest lemma.
In the non-generic case, just insert `"#[k]"` before the call argument
list where k is the number of recursion levels.

In the case where the `greatest lemma` is generic, the generic type
argument is given before. Here is an example:

<!-- %check-verify -->
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

greatest predicate atmost(a: Stream, b: Stream)
{
  match a
  case Nil => true
  case Cons(h,s,t) => b.Cons? && h <= b.head && atmost(t, b.tail)
}

greatest lemma {:induction false} Theorem0<T>(s: T)
  ensures atmost(zeros(s), ones(s))
{
  // the following shows two equivalent ways to state the
  // coinductive hypothesis
  if (*) {
    Theorem0#<T>[_k-1](s);
  } else {
    Theorem0(s);
  }
}
```

where the ``HashCall`` is `"Theorem0#<T>[_k-1](s);"`.
See [Section 5.14.3.5](#sec-copredicates) and [Section 5.14.3.6.3](#sec-prefix-lemmas).

## 9.34. Suffix ([grammar](#g-suffix)) {#sec-suffix}

A _suffix_ describes ways of deriving a new value from
the entity to which the suffix is appended. The several kinds
of suffixes are described below.

### 9.34.1. Augmented Dot Suffix ([grammar](#g-augmented-dot-suffix)) {#sec-augmented-dot-suffix}

Examples: (expression with suffix)
<!-- %no-check -->
```dafny
a.b
(a).b<int>
a.b#[k]
a.b#<int>[k]
```

An augmented dot suffix consists of a simple [dot suffix](#sec-identifier-variations) optionally
followed by either

* a ``GenericInstantiation`` (for the case where the item
selected by the ``DotSuffix`` is generic), or
* a ``HashCall`` for the case where we want to call a prefix predicate
  or prefix lemma. The result is the result of calling the prefix predicate
  or prefix lemma.

### 9.34.2. Datatype Update Suffix ([grammar](#g-datatype-update-suffix)) {#sec-datatype-update-suffix}

Examples: (expression with suffix)
<!-- %no-check -->
```dafny
a.(f := e1, g:= e2)
a.(0 := e1)
(e).(f := e1, g:= e2)
```

A _datatype update suffix_ is used to produce a new datatype value
that is the same as an old datatype value except that the
value corresponding to a given destructor has the specified value.
In a _member binding update_, the given identifier (or digit sequence) is the
name of a destructor (i.e. the formal parameter name) for one of the
constructors of the datatype. The expression to the right of the
`:=` is the new value for that formal.

All of the destructors in a datatype update suffix must be
for the same constructor, and if they do not cover all of the
destructors for that constructor then the datatype value being
updated must have a value derived from that same constructor.

Here is an example:

<!-- %check-verify Expressions.4.expect -->
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
    ensures def == datum.(otherbool := !datum.mybool)  // error
    ensures ghi == datum.(myint := 2).(mybool := false)
    // Resolution error: no non_destructor in MyDataType
    //ensures jkl == datum.(non_destructor := 5) // error
    ensures jkl == datum.(42 := 7)
  {
    abc := MyConstructor(x + 2, datum.mybool);
    abc := datum.(myint := x + 2);
    def := MyOtherConstructor(!datum.mybool);
    ghi := MyConstructor(2, false);
    jkl := datum.(42 := 7); // error

    assert abc.(myint := abc.myint - 2) == datum.(myint := x);
  }
}
```

### 9.34.3. Subsequence Suffix ([grammar](#g-subsequence-suffix)) {#sec-subsequence-suffix}

Examples: (with leading expression)
<!-- %no-check -->
```dafny
a[lo .. hi ]
(e)[ lo .. ]
e[ .. hi ]
e[ .. ]
```

A subsequence suffix applied to a sequence produces a new sequence whose
elements are taken from a contiguous part of the original sequence. For
example, expression `s[lo..hi]` for sequence `s`, and integer-based
numeric bounds `lo` and `hi` satisfying `0 <= lo <= hi <= |s|`. See
[the section about other sequence expressions](#sec-other-sequence-expressions) for details.

A subsequence suffix applied to an array produces a _sequence_ consisting of 
the values of the designated elements. A concise way of converting a whole 
array to a sequence is to write `a[..]`.

### 9.34.4. Subsequence Slices Suffix ([grammar](#g-subsequence-slices-suffix)) {#sec-subsequence-slices-suffix}

Examples: (with leading expression)
<!-- %no-check -->
```dafny
a[ 0 : 2 : 3 ]
a[ e1 : e2 : e3 ]
a[ 0 : 2 : ]
```

Applying a _subsequence slices suffix_ to a sequence produces a
sequence of subsequences of the original sequence.
See [the section about other sequence expressions](#sec-other-sequence-expressions) for details.

### 9.34.5. Sequence Update Suffix ([grammar](#g-sequence-update-suffix)) {#sec-sequence-update-suffix}

Examples:
<!-- %no-check -->
```dafny
s[1 := 2, 3 := 4]
```

For a sequence `s` and expressions `i` and `v`, the expression
`s[i := v]` is the same as the sequence `s` except that at
index `i` it has value `v`.

If the type of `s` is `seq<T>`, then `v` must have type `T`.
The index `i` can have any integer- or bit-vector-based type
(this is one situation in which Dafny implements implicit
conversion, as if an `as int` were appended to the index expression).
The expression `s[i := v]` has the same type as `s`.

### 9.34.6. Selection Suffix ([grammar](#g-selection-suffix)) {#sec-selection-suffix}

Examples:
<!-- %no-check -->
```dafny
a[9]
a[i.j.k]
```

If a selection suffix  has only one expression in it, it is a
zero-based index that may be used to select a single element of a
sequence or from a single-dimensional array.

If a selection suffix has more than one expression in it, then
it is a list of indices to index into a multi-dimensional array.
The rank of the array must be the same as the number of indices.

If the selection suffix is used with an array or a sequence,
then each index expression can have any integer- or bit-vector-based
type
(this is one situation in which Dafny implements implicit
conversion, as if an `as int` were appended to the index expression).

### 9.34.7. Argument List Suffix ([grammar](#g-argument-list-suffix)) {#sec-argument-list-suffix}

Examples:
<!-- %no-check -->
```dafny
()
(a)
(a, b)
```
An argument list suffix is a parenthesized list of expressions that
are the arguments to pass to a method or function that is being
called. Applying such a suffix causes the method or function
to be called and the result is the result of the call.

Note that method calls may only appear in [right-hand-side](#sec-rhs-expression)
locations, whereas function calls may appear in expressions and specifications;
this distinction can be made only during name and type resolution, not by the
parser.

## 9.35. Expression Lists ([grammar](#g-expression-list)) {#sec-expression-list}

Examples:
<!-- %no-check -->
```dafny
                // empty list
a
a, b
```

An expression list is a comma-separated sequence of expressions, used, for example,
as actual araguments in a method or function call or in parallel assignment.

## 9.36. Parameter Bindings ([grammar](#g-parameter-bindings)) {#sec-parameter-bindings}

Examples: 
<!-- %no-check -->
```dafny
a
a, b
a, optimize := b
```

Method calls, object-allocation calls (`new`), function calls, and
datatype constructors can be called with both positional arguments
and named arguments.

Formal parameters have three ways to indicate how they are to be passed in:
- nameonly: the only way to give a specific argument value is to name the parameter
- positional only: these are nameless parameters (which are allowed only for datatype constructor parameters)
- either positional or by name: this is the most common parameter

A parameter is either required or optional:
- required: a caller has to supply an argument
- optional: the parameter has a default value that is used if a caller omits passing a specific argument

The syntax for giving a positional-only (i.e., nameless) parameter does not allow a default-value expression, so a positional-only parameter is always required.

At a call site, positional arguments are not allowed to follow named arguments. Therefore, if `x` is a nameonly parameter, then there is no way to supply the parameters after `x` by position. 
Thus, any parameter that follows `x` must either be passed by name or have a default value. 
That is, if a later (in the formal parameter declaration) parameter does not have a default value, it is effectively nameonly. 

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

## 9.37. Assigned Expressions {#sec-assigned-expression}

Examples:
<!-- %no-check -->
```dafny
assigned(x)
```

For any variable, constant, out-parameter, or object field `x`,
the expression `assigned(x)` evaluates to `true` in a state
if `x` is definitely assigned in that state.

See [Section 12.6](#sec-definite-assignment) for more details on definite assignment.

## 9.38. Termination Ordering Expressions {#sec-termination-ordering-expressions}

When proving that a loop or recursive callable terminates, Dafny
automatically generates a proof obligation that the sequence of
expressions listed in a `decreases` clause gets smaller (in the
[lexicographic termination ordering](#sec-decreases-clause)) with each
iteration or recursive call. Normally, this proof obligation is purely
internal. However, it can be written as a Dafny expression using the
`decreases to` operator.

The Boolean expression `(a, ..., b decreases to a', ..., b')` encodes
this ordering. (The parentheses can be omitted if there is exactly 1 left-hand side
and exactly 1 right-hand side.) For example, the following assertions are valid:
<!-- %check-verify -->
```dafny
method M(x: int, y: int) {
  assert 1 decreases to 0;
  assert (true, false decreases to false, true);
  assert (x, y decreases to x - 1, y);
}
```

Conversely, the following assertion is invalid:
<!-- %check-verify Expressions.5.expect -->
```dafny
method M(x: int, y: int) {
  assert x decreases to x + 1;
}
```

The `decreases to` operator is strict, that is, it means "strictly greater than".
The `nonincreases to` operator is the non-strict ("greater than or equal") version of it.

## 9.39. Compile-Time Constants {#sec-compile-time-constants}

In certain situations in Dafny it is helpful to know what the value of a
constant is during program analysis, before verification or execution takes
place. For example, a compiler can choose an optimized representation of a
`newtype` that is a subset of `int` if it knows the range of possible values
of the subset type: if the range is within 0 to less than 256, then an
unsigned 8-bit representation can be used.

To continue this example, suppose a new type is defined as
<!-- %check-resolve -->
```dafny
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
- real operations: `+ - *` and unary `-` and comparisons `< <= > >= == !=`
- bool operations: `&& || ==> <== <==> == !=` and unary `!`
- bit-vector operations: `+ - * / % << >> & | ^` and unary `! -` and comparisons `< <= > >= == !=`
- char operations: `< <= > >= == !=`
- string operations: length: `|...|`, concatenation: `+`, comparisons `< <= == !=`, indexing `[]`
- conversions between: `int` `real` `char` bit-vector
- newtype operations: newtype arguments, but not newtype results
- symbolic values that are declared `const` and have an explicit initialization value that is a compile-time constant
- conditional (if-then-else) expressions
- parenthesized expressions

[^CTC]: This set of operations that are constant-folded may be enlarged in future versions of `dafny`.

## 9.40. List of specification expressions {#sec-list-of-specification-expressions}

The following is a list of expressions that can only appear in specification contexts or in ghost blocks.

* [Fresh expressions](#sec-fresh-expression)
* [Allocated expressions](#sec-allocated-expression)
* [Unchanged expressions](#sec-unchanged-expression)
* [Old expressions](#sec-old-expression)
- [Assigned expressions](#sec-assigned-expression)
* [Assert and calc expressions](#sec-statement-in-an-expression)
* [Hash Calls](#sec-hash-call)
* [Termination ordering expression](#sec-termination-ordering-expressions)
