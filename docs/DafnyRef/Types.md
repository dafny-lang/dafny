# 5. Types {#sec-types}

A Dafny type is a (possibly-empty) set of values or heap data-structures,
together with allowed operations on those values.
Types are classified as mutable reference types or immutable value types,
depending on whether their values are stored in the heap or are 
(mathematical) values independent of the heap.

Dafny supports the following kinds of types,
all described in later sections of this manual:
* [builtin scalar types](#sec-basic-type), 
* [builtin collection types](#sec-collection-types), 
* [reference types](#sec-class-types) (classes, traits, iterators),
* [tuple types](#sec-tuple-types) (including as a special case a parenthesized type),
* [inductive](#sec-datatype) and [coinductive](#sec-coinductive-datatypes) datatypes, 
* [function (arrow) types](#sec-arrow-subset-types), and
* [types, such as subset types, derived from other types](#sec-subset-types).

## 5.1. Kinds of types
### 5.1.1. Value Types
The value types are those whose values do not lie in the program heap.
These are:

* The basic scalar types: `bool`, `char`, `int`, `real`, `ORDINAL`, bitvector types
* The built-in collection types: `set`, `iset`, `multiset`, `seq`, `string`, `map`, `imap`
* Tuple Types
* Inductive and coinductive types
* Function (arrow) types
* Subset and newtypes that are based on value types

Data items having value types are passed by value. Since they are not
considered to occupy _memory_, framing expressions do not reference them.

The `nat` type is a pre-defined [subset type](#sec-subset-types) of `int`.

Dafny does not include types themselves as values, nor is there a type of types.

### 5.1.2. Reference Types {#sec-reference-types}
Dafny offers a host of _reference types_.  These represent
_references_ to objects allocated dynamically in the program heap.  To
access the members of an object, a reference to (that is, a _pointer_
to or _object identity_ of) the object is _dereferenced_.

The reference types are class types, traits and array types.
Dafny supports both reference types that contain the special `null` value
(_nullable types_) and reference types that do not (_non-null types_).

### 5.1.3. Named Types ([grammar](#g-type))

A _Named Type_ is used to specify a user-defined type by name
(possibly module-qualified). Named types are introduced by
class, trait, inductive, coinductive, synonym and opaque
type declarations. They are also used to refer to type variables.
A Named Type is denoted by a dot-separated sequence of `NameSegmentForTypeName`s

A ``NameSegmentForTypeName`` is a type name optionally followed by a
``GenericInstantiation``, which supplies type parameters to a generic
type, if needed. It is a special case of a ``NameSegment``
([Section 9.32](#sec-name-segment))
that does not allow a ``HashCall``.

The following sections describe each of these kinds of types in more detail.

<!--PDF NEWPAGE-->
## 5.2. Basic types {#sec-basic-type}

Dafny offers these basic types: `bool` for booleans, `char` for
characters, `int` and `nat` for integers, `real` for reals,
`ORDINAL`, and bit-vector types.

### 5.2.1. Booleans ([grammar](#g-basic-type)) {#sec-booleans}

There are two boolean values and each has a corresponding literal in
the language:  `false` and `true`.

Type `bool` supports the following operations:

 operator           | precedence | description
--------------------|:----------:|------------------------------------
 `<==>`             | 1 | equivalence (if and only if)
--------------------|------------------------------------
 `==>`              | 2 | implication (implies)
 `<==`              | 2 | reverse implication (follows from)
--------------------|------------------------------------
 `&&`               | 3 | conjunction (and)
 `||`               | 3 |  disjunction (or)
--------------------|------------------------------------
 `==`               | 4 | equality
 `!=`               | 4 | disequality
--------------------|------------------------------------
 `!`                | 10 | negation (not)

Negation is unary; the others are binary.  The table shows the operators
in groups of increasing binding power, with equality binding stronger
than conjunction and disjunction, and weaker than negation.  Within
each group, different operators do not associate, so parentheses need
to be used.  For example,
<!-- %no-check -->
```dafny
A && B || C    // error
```
would be ambiguous and instead has to be written as either
<!-- %no-check -->
```dafny
(A && B) || C
```
or
<!-- %no-check -->
```dafny
A && (B || C)
```
depending on the intended meaning.

#### 5.2.1.1. Equivalence Operator {#sec-equivalence-operator}

The expressions `A <==> B` and `A == B` give the same value, but note
that `<==>` is _associative_ whereas `==` is _chaining_ and they have
different precedence.  So,
<!-- %no-check -->
```dafny
A <==> B <==> C
```
is the same as
<!-- %no-check -->
```dafny
A <==> (B <==> C)
```
and
<!-- %no-check -->
```dafny
(A <==> B) <==> C
```
whereas
<!-- %no-check -->
```dafny
A == B == C
```
is simply a shorthand for
<!-- %no-check -->
```dafny
A == B && B == C
```

#### 5.2.1.2. Conjunction and Disjunction {#sec-conjunction-and-disjunction}

Conjunction and disjunction are associative.  These operators are
_short circuiting (from left to right)_, meaning that their second
argument is evaluated only if the evaluation of the first operand does
not determine the value of the expression.  Logically speaking, the
expression `A && B` is defined when `A` is defined and either `A`
evaluates to `false` or `B` is defined.  When `A && B` is defined, its
meaning is the same as the ordinary, symmetric mathematical
conjunction `&`.  The same holds for `||` and `|`.

#### 5.2.1.3. Implication and  Reverse Implication {#sec-implication-and-reverse-implication}

Implication is _right associative_ and is short-circuiting from left
to right.  Reverse implication `B <== A` is exactly the same as
`A ==> B`, but gives the ability to write the operands in the opposite
order.  Consequently, reverse implication is _left associative_ and is
short-circuiting from _right to left_.  To illustrate the
associativity rules, each of the following four lines expresses the
same property, for any `A`, `B`, and `C` of type `bool`:
<!-- %no-check -->
```dafny
A ==> B ==> C
A ==> (B ==> C) // parentheses redundant, ==> is right associative
C <== B <== A
(C <== B) <== A // parentheses redundant, <== is left associative
```
To illustrate the short-circuiting rules, note that the expression
`a.Length` is defined for an array `a` only if `a` is not `null` (see
[Section 5.1.2](#sec-reference-types)), which means the following two
expressions are well-formed:
<!-- %no-check -->
```dafny
a != null ==> 0 <= a.Length
0 <= a.Length <== a != null
```
The contrapositives of these two expressions would be:
<!-- %no-check -->
```dafny
a.Length < 0 ==> a == null  // not well-formed
a == null <== a.Length < 0  // not well-formed
```
but these expressions are not well-formed, since well-formedness
requires the left (and right, respectively) operand, `a.Length < 0`,
to be well-formed by itself.

Implication `A ==> B` is equivalent to the disjunction `!A || B`, but
is sometimes (especially in specifications) clearer to read.  Since,
`||` is short-circuiting from left to right, note that
<!-- %no-check -->
```dafny
a == null || 0 <= a.Length
```
is well-formed, whereas
<!-- %no-check -->
```dafny
0 <= a.Length || a == null  // not well-formed
```
is not.

In addition, booleans support _logical quantifiers_ (forall and
exists), described in [Section 9.31.4](#sec-quantifier-expression).

### 5.2.2. Numeric Types ([grammar](#g-basic-type)) {#sec-numeric-types}

Dafny supports _numeric types_ of two kinds, _integer-based_, which
includes the basic type `int` of all integers, and _real-based_, which
includes the basic type `real` of all real numbers.  User-defined
numeric types based on `int` and `real`, either _subset types_ or _newtypes_,
are described in [Section 5.6.3](#sec-subset-types) and [Section 5.7](#sec-newtypes).

There is one built-in [_subset type_](#sec-subset-types),
`nat`, representing the non-negative subrange of `int`.

The language includes a literal for each integer, like
`0`, `13`, and `1985`.  Integers can also be written in hexadecimal
using the prefix "`0x`", as in `0x0`, `0xD`, and `0x7c1` (always with
a lower case `x`, but the hexadecimal digits themselves are case
insensitive).  Leading zeros are allowed.  To form negative literals,
use the unary minus operator, as in `-12`, but not `-(12)`.

There are also literals for some of the reals.  These are
written as a decimal point with a nonempty sequence of decimal digits
on both sides, optionally prefixed by a `-` character.
For example, `1.0`, `1609.344`, `-12.5`, and `0.5772156649`.
Real literals using exponents are not supported in Dafny. For now, you'd have to write your own function for that, e.g. 
<!-- %check-verify -->
```dafny
// realExp(2.37, 100) computes 2.37e100
function method realExp(r: real, e: int): real decreases if e > 0 then e else -e {
  if e == 0 then r
  else if e < 0 then realExp(r/10.0, e+1)
  else realExp(r*10.0, e-1)
}
```

For integers (in both decimal and hexadecimal form) and reals,
any two digits in a literal may be separated by an underscore in order
to improve human readability of the literals.  For example:
<!-- %check-verify -->
```dafny
const c1 := 1_000_000        // easier to read than 1000000
const c2 := 0_12_345_6789    // strange but legal formatting of 123456789
const c3 := 0x8000_0000      // same as 0x80000000 -- hex digits are
                             // often placed in groups of 4
const c4 := 0.000_000_000_1  // same as 0.0000000001 -- 1 Angstrom
```

In addition to equality and disequality, numeric types
support the following relational operations, which have the
same precedence as equality:

 operator          | description
-------------------|------------------------------------
  `<`              | less than
  `<=`             | at most
  `>=`             | at least
  `>`              | greater than

Like equality and disequality, these operators are chaining, as long
as they are chained in the "same direction".  That is,
<!-- %no-check -->
```dafny
A <= B < C == D <= E
```
is simply a shorthand for
<!-- %no-check -->
```dafny
A <= B && B < C && C == D && D <= E
```
whereas
<!-- %no-check -->
```dafny
A < B > C
```
is not allowed.

There are also operators on each numeric type:

 operator        | precedence | description
-----------------|:---:|------------------------------------
  `+`            | 6 | addition (plus)
  `-`            | 6 | subtraction (minus)
-----------------|------------------------------------
  `*`            | 7 | multiplication (times)
  `/`            | 7 | division (divided by)
  `%`            | 7 | modulus (mod)  -- int only
-----------------|------------------------------------
  `-`            | 10 | negation (unary minus)

The binary operators are left associative, and they associate with
each other in the two groups.
The groups are listed in order of
increasing binding power, with equality binding less strongly than any of these operators.
There is no implicit conversion between `int` and `real`: use `as int` or
`as real` conversions to write an explicit conversion (cf. [Section 9.10](#sec-as-is-expression)).

Modulus is supported only for integer-based numeric types.  Integer
division and modulus are the _Euclidean division and modulus_.  This
means that modulus always returns a non-negative value, regardless of the
signs of the two operands.  More precisely, for any integer `a` and
non-zero integer `b`,
<!-- %no-check -->
```dafny
a == a / b * b + a % b
0 <= a % b < B
```
where `B` denotes the absolute value of `b`.

Real-based numeric types have a member `Floor` that returns the
_floor_ of the real value (as an int value), that is, the largest integer not exceeding
the real value.  For example, the following properties hold, for any
`r` and `r'` of type `real`:
<!-- %check-verify -->
```dafny
method m(r: real, r': real) {
  assert 3.14.Floor == 3;
  assert (-2.5).Floor == -3;
  assert -2.5.Floor == -2; // This is -(2.5.Floor)
  assert r.Floor as real <= r;
  assert r <= r' ==> r.Floor <= r'.Floor;
}
```
Note in the third line that member access (like `.Floor`) binds
stronger than unary minus.  The fourth line uses the conversion
function `as real` from `int` to `real`, as described in
[Section 9.10](#sec-as-is-expression).

### 5.2.3. Bit-vector Types ([grammar](#g-basic-type)) {#sec-bit-vector-types}

Dafny includes a family of bit-vector types, each type having a specific,
constant length, the number of bits in its values.
Each such type is
distinct and is designated by the prefix `bv` followed (without white space) by
a positive integer without leading zeros or zero, stating the number of bits. For example,
`bv1`, `bv8`, and `bv32` are legal bit-vector type names.
The type `bv0` is also legal; it is a bit-vector type with no bits and just one value, `0x0`.

Constant literals of bit-vector types are given by integer literals converted automatically
to the designated type, either by an implicit or explicit conversion operation or by initialization in a declaration.
Dafny checks that the constant literal is in the correct range. For example,
<!-- %check-resolve Types.1.expect -->
```dafny
const i: bv1 := 1
const j: bv8 := 195
const k: bv2 := 5 // error - out of range
const m := (194 as bv8) | (7 as bv8)
```

Bit-vector values can be converted to and from `int` and other bit-vector types, as long as
the values are in range for the target type. Bit-vector values are always considered unsigned.

Bit-vector operations include bit-wise operators and arithmetic operators
(as well as equality, disequality, and comparisons).
The arithmetic operations
truncate the high-order bits from the results; that is, they perform
unsigned arithmetic modulo 2^{number of bits}, like 2's-complement machine arithmetic.

 operator        | precedence | description
-----------------|:---:|------------------------------------
 `<<`            | 5 | bit-limited bit-shift left
 `>>`            | 5 | unsigned bit-shift right
-----------------|------------------------------------
  `+`            | 6 | bit-limited addition
  `-`            | 6 | bit-limited subtraction
-----------------|------------------------------------
  `*`            | 7 | bit-limited multiplication
-----------------|------------------------------------
  `&`            | 8 | bit-wise and
  `|`            | 8 | bit-wise or 
  `^`            | 8 | bit-wise exclusive-or
-----------------|------------------------------------
  `-`            | 10 | bit-limited negation (unary minus)
  `!`            | 10 | bit-wise complement
-----------------|------------------------------------
  .RotateLeft(n) | 11 | rotates bits left by n bit positions
  .RotateRight(n)| 11 | rotates bits right by n bit positions

The groups of operators lower in the table above bind more tightly.[^binding]
All operators bind more tightly than equality, disequality, and comparisons.
All binary operators are left-associative, but the 
bit-wise `&`, `|`, and `^` do not associate together (parentheses are required to disambiguate).
The `+`, `|`, `^`, and `&` operators are commutative.

The right-hand operand of bit-shift operations is an `int` value,
must be non-negative, and
no more than the number of bits in the type.
There is no signed right shift as all bit-vector values correspond to
non-negative integers.

Bit-vector negation returns an unsigned value in the correct range for the type.
It has the properties `x + (-x) == 0` and `(!x) + 1 == -x`, for a bitvector value `x`
of at least one bit.

The argument of the `RotateLeft` and `RotateRight` operations is a
non-negative `int` that is no larger than the bit-width of the value being rotated.
`RotateLeft` moves bits to higher bit positions (e.g., `(2 as bv4).RotateLeft(1) == (4 as bv4)`
and `(8 as bv4).RotateLeft(1) == (1 as bv4)`);
`RotateRight` moves bits to lower bit positions, so `b.RotateLeft(n).RotateRight(n) == b`.

Here are examples of the various operations (all the assertions are true except where indicated):
<!-- %check-verify -->
```dafny
const i: bv4 := 9
const j: bv4 := 3

method m() {
  assert (i & j) == (1 as bv4);
  assert (i | j) == (11 as bv4);
  assert (i ^ j) == (10 as bv4);
  assert !i == (6 as bv4);
  assert -i == (7 as bv4);
  assert (i + i) == (2 as bv4);
  assert (j - i) == (10 as bv4);
  assert (i * j) == (11 as bv4);
  assert (i as int) / (j as int) == 3;
  assert (j << 1) == (6 as bv4);
  assert (i << 1) == (2 as bv4);
  assert (i >> 1) == (4 as bv4);
  assert i == 9; // auto conversion of literal to bv4
  assert i * 4 == j + 8 + 9; // arithmetic is modulo 16
  assert i + j >> 1 == (i + j) >> 1; // + - bind tigher than << >>
  assert i + j ^ 2 == i + (j^2);
  assert i * j & 1 == i * (j&1); // & | ^ bind tighter than + - *
}
```
The following are incorrectly formed:
<!-- %check-resolve Types.2.expect -->
```dafny
const i: bv4 := 9
const j: bv4 := 3

method m() {
  assert i & 4 | j == 0 ; // parentheses required
}
```
<!-- %check-resolve Types.3.expect -->
```dafny
const k: bv4 := 9

method p() {
  assert k as bv5 == 9 as bv6; // error: mismatched types
}
```
These produce assertion errors:
<!-- %check-verify Types.4.expect -->
```dafny
const i: bv4 := 9

method m() {
  assert i as bv3 == 1; // error: i is out of range for bv3
}
```
<!-- %check-resolve Types.5.expect -->
```dafny
const j: bv4 := 9

method n() {
  assert j == 25; // error: 25 is out of range for bv4
}
```

Bit-vector constants (like all constants) can be initialized using expressions, but pay attention
to how type inference applies to such expressions. For example,
<!-- %check-verify -->
```dafny
const a: bv3 := -1
```
is legal because Dafny interprets `-1` as a `bv3` expression, because `a` has type `bv3`.
Consequently the `-` is `bv3` negation and the `1` is a `bv3` literal; the value of the expression `-1` is
the `bv3` value `7`, which is then the value of `a`.

On the other hand,
<!-- %check-resolve Types.6.expect -->
```dafny
const b: bv3 := 6 & 11
```
is illegal because, again, the `&` is `bv3` bit-wise-and and the numbers must be valid `bv3` literals.
But `11` is not a valid `bv3` literal.

[^binding]: The binding power of shift and bit-wise operations is different than in C-like languages.

### 5.2.4. Ordinal type ([grammar](#g-basic-type)) {#sec-ordinals}

Values of type `ORDINAL` behave like `nat`s in many ways, with one important difference:
there are `ORDINAL` values that are larger than any `nat`. The smallest of these non-nat ordinals is
represented as $\omega$ in mathematics, though there is no literal expression in Dafny that represents this value.

The natural numbers are ordinals.
Any ordinal has a successor ordinal (equivalent to adding `1`).
Some ordinals are _limit_ ordinals, meaning they are not a successor of any other ordinal;
the natural number `0` and  $\omega$ are limit ordinals.

The _offset_ of an ordinal is the number of successor operations it takes to reach it from a limit ordinal.

The Dafny type `ORDINAL` has these member functions:
- `o.IsLimit` -- true if `o` is a limit ordinal (including `0`)
- `o.IsSucc` -- true if `o` is a successor to something, so `o.IsSucc <==> !o.IsLimit`
- `o.IsNat` -- true if `o` represents a `nat` value, so for `n` a `nat`, `(n as ORDINAL).IsNat` is true
and if `o.IsNat` is true then `(o as nat)` is well-defined
- `o.Offset` -- is the `nat` value giving the offset of the ordinal

In addition, 
- non-negative numeric literals may be considered `ORDINAL` literals, so `o + 1` is allowed
- `ORDINAL`s may be compared, using `== != < <= > >=`
- two `ORDINAL`s may be added and the result is `>=` either one of them; addition is associative but not commutative
- `*`, `/` and `%` are not defined for `ORDINAL`s
- two `ORDINAL`s may be subtracted if the RHS satisfies `.IsNat` and the offset of the LHS is not smaller than the offset of the RHS

In Dafny, `ORDINAL`s are used primarily in conjunction with [extreme functions and lemmas](#sec-extreme).

### 5.2.5. Characters ([grammar](#g-basic-type)) {#sec-characters}

Dafny supports a type `char` of _characters_.  
Its exact meaning is controlled by the command-line switch `--unicode-char:true|false`.

If `--unicode-char` is disabled, then `char` represents any [UTF-16 code unit](https://en.wikipedia.org/wiki/UTF-16).
This includes surrogate code points.

If `--unicode-char` is enabled, then `char` represents any [Unicode scalar value](https://unicode.org/glossary/#unicode_scalar_value).
This excludes surrogate code points.

Character literals are enclosed in single quotes, as in `'D'`. 
To write a single quote as a
character literal, it is necessary to use an _escape sequence_.
Escape sequences can also be used to write other characters.  The
supported escape sequences are the following:

 escape sequence    | meaning
--------------------|-------------------------------------------------------
 `\'`               | the character `'`
 `\"`               | the character `"`
 `\\`               | the character `\`
 `\0`               | the null character, same as `\u0000` or `\U{0}`
 `\n`               | line feed
 `\r`               | carriage return
 `\t`               | horizontal tab
 `\u`_xxxx_         | [UTF-16 code unit](https://en.wikipedia.org/wiki/UTF-16) whose hexadecimal code is _xxxx_,  where each _x_ is a hexadecimal digit
 `\U{`_x..x_`}`     | [Unicode scalar value](https://unicode.org/glossary/#unicode_scalar_value) whose hexadecimal code is _x..x_,  where each _x_ is a hexadecimal digit

The escape sequence for a double quote is redundant, because
`'"'` and `'\"'` denote the same
character---both forms are provided in order to support the same
escape sequences in string literals ([Section 5.5.3.5](#sec-strings)).

In the form `\u`_xxxx_, which is only allowed if `--unicode-char` is disabled,
the `u` is always lower case, but the four
hexadecimal digits are case insensitive.

In the form `\U{`_x..x_`}`, 
which is only allowed if `--unicode-char` is enabled,
the `U` is always upper case,
but the hexadecimal digits are case insensitive, and there must
be at least one and at most six digits.
Surrogate code points are not allowed.
The hex digits may be interspersed with underscores for readability 
(but not beginning or ending with an underscore), as in `\U{1_F680}`.

Character values are ordered and can be compared using the standard
relational operators:

 operator        | description
-----------------|-----------------------------------
  `<`              | less than
  `<=`             | at most
  `>=`             | at least
  `>`              | greater than

Sequences of characters represent _strings_, as described in
[Section 5.5.3.5](#sec-strings).

Character values can be converted to and from `int` values using the
`as int` and `as char` conversion operations. The result is what would
be expected in other programming languages, namely, the `int` value of a
`char` is the ASCII or Unicode numeric value.

The only other operations on characters are obtaining a character
by indexing into a string, and the implicit conversion to string
when used as a parameter of a `print` statement.

<!--PDF NEWPAGE-->
## 5.3. Type parameters ([grammar](#g-type-parameter)) {#sec-type-parameters}

Examples:
<!-- %check-resolve -->
```dafny
type G1<T>
type G2<T(0)>
type G3<+T(==),-U>
```

Many of the types, functions, and methods in Dafny can be
parameterized by types.  These _type parameters_ are 
declared inside angle brackets and can stand for any type.

Dafny has some inference support that makes certain signatures less
cluttered (described in [Section 12.2](#sec-type-inference)).

### 5.3.1. Declaring restrictions on type parameters {#sec-type-characteristics}

It is sometimes necessary to restrict type parameters so that
they can only be instantiated by certain families of types, that is,
by types that have certain properties. These properties are known as
_type characteristics_. The following subsections
describe the type characteristics that Dafny supports.

In some cases, type inference will infer that a type-parameter
must be restricted in a particular way, in which case Dafny
will add the appropriate suffix, such as `(==)`, automatically.

If more than one restriction is needed, they are either
listed comma-separated,
inside the parentheses or as multiple parenthesized elements:
 `T(==,0)` or `T(==)(0)`.

#### 5.3.1.1. Equality-supporting type parameters: `T(==)` {#sec-equality-supporting}

Designating a type parameter with the `(==)` suffix indicates that
the parameter may only be replaced in non-ghost contexts
with types that are known to
support run-time equality comparisons (`==` and `!=`).
All types support equality in ghost contexts,
as if, for some types, the equality function is ghost.

For example,
<!-- %check-verify -->
```dafny
method Compare<T(==)>(a: T, b: T) returns (eq: bool)
{
  if a == b { eq := true; } else { eq := false; }
}
```
is a method whose type parameter is restricted to equality-supporting
types when used in a non-ghost context.
Again, note that _all_ types support equality in _ghost_
contexts; the difference is only for non-ghost (that is, compiled)
code.  Coinductive datatypes, arrow types, and inductive
datatypes with ghost parameters are examples of types that are not
equality supporting.

#### 5.3.1.2. Auto-initializable types: `T(0)` {#sec-auto-init}

At every access of a variable `x` of a type `T`, Dafny ensures that
`x` holds a legal value of type `T`.
If no explicit initialization is given, then an arbitrary value is
assumed by the verifier and supplied by the compiler,
that is, the variable is _auto-initialized_.
For example,
<!-- %check-verify Types.7a.expect %options --relax-definite-assignment -->
```dafny
method m() {
  var n: nat; // Auto-initialized to an arbitrary value of type `nat`
  assert n >= 0; // true, regardless of the value of n
  var i: int;
  assert i >= 0; // possibly false, arbitrary ints may be negative
}
```

For some types (known as _auto-init types_), the compiler can choose an
initial value, but for others it does not.
Variables and fields whose type the compiler does not auto-initialize
are subject to _definite-assignment_ rules. These ensure that the program
explicitly assigns a value to a variable before it is used.
For more details see [Section 12.6](#sec-definite-assignment) and the `--strict-definite-assignment` command-line option.
More detail on auto-initializing is in [this document](../Compilation/AutoInitialization).

Dafny supports auto-init as a type characteristic.
To restrict a type parameter to auto-init types, mark it with the
`(0)` suffix. For example,
<!-- %check-verify Types.7b.expect %options --relax-definite-assignment -->
```dafny
method AutoInitExamples<A(0), X>() returns (a: A, x: X)
{
  // 'a' does not require an explicit initialization, since A is auto-init
  // error: out-parameter 'x' has not been given a value
}
```
In this example, an error is reported because out-parameter `x` has not
been assigned---since nothing is known about type `X`, variables of
type `X` are subject to definite-assignment rules. In contrast, since
type parameter `A` is declared to be restricted to auto-init types,
the program does not need to explicitly assign any value to the
out-parameter `a`.

#### 5.3.1.3. Nonempty types: `T(00)` {#sec-nonempty-types}

Auto-init types are important in compiled contexts. In ghost contexts, it
may still be important to know that a type is nonempty. Dafny supports
a type characteristic for nonempty types, written with the suffix `(00)`.
For example,
<!-- %check-verify Types.8.expect %options --relax-definite-assignment -->
```dafny
method NonemptyExamples<B(00), X>() returns (b: B, ghost g: B, ghost h: X)
{
  // error: non-ghost out-parameter 'b' has not been given a value
  // ghost out-parameter 'g' is fine, since its type is nonempty
  // error: 'h' has not been given a value
}
```
Because of `B`'s nonempty type characteristic, ghost parameter `g` does not
need to be explicitly assigned. However, Dafny reports an error for the
non-ghost `b`, since `B` is not an auto-init type, and reports an error
for `h`, since the type `X` could be empty.

Note that every auto-init type is nonempty.

#### 5.3.1.4. Non-heap based: `T(!new)` {#sec-non-heap-based}

Dafny makes a distinction between types whose values are on the heap,
i.e. references, like
classes and arrays, and those that are strictly value-based, like basic
types and datatypes.
The practical implication is that references depend on allocation state
(e.g., are affected by the `old` operation) whereas non-reference values
are not.
Thus it can be relevant to know whether the values of a type parameter
are heap-based or not. This is indicated by the mode suffix `(!new)`.

A type parameter characterized by `(!new)` is _recursively_ independent
of the allocation state. For example, a datatype is not a reference, but for
a parameterized data type such as
<!-- %check-resolve -->
```dafny
datatype Result<T> = Failure(error: string) | Success(value: T)
```
the instantiation `Result<int>` satisfies `(!new)`, whereas
`Result<array<int>>` does not.

Note that this characteristic of a type parameter is operative for both
verification and compilation.
Also, opaque types at the topmost scope are always implicitly `(!new)`.

Here are some examples:
<!-- %check-resolve Types.9.expect -->
```dafny
datatype Result<T> = Failure(error: string) | Success(v: T)
datatype ResultN<T(!new)> = Failure(error: string) | Success(v: T)

class C {}

method m() {
  var x1: Result<int>;
  var x2: ResultN<int>;
  var x3: Result<C>;
  var x4: ResultN<C>; // error
  var x5: Result<array<int>>;
  var x6: ResultN<array<int>>; // error
}
```

### 5.3.2. Type parameter variance {#sec-type-parameter-variance}

Type parameters have several different variance and cardinality properties.
These properties of type parameters are designated in a generic type definition.
For instance, in `type A<+T> = ... `, the `+` indicates that the `T` position
is co-variant. These properties are indicated by the following notation:

notation | variance | cardinality-preserving
:-------:|----------|-----------------------
(nothing) | non-variant | yes
`+`      | co-variant | yes
`-`      | contra-variant | not necessarily
`*`      | co-variant | not necessarily
`!`      | non-variant | not necessarily

- _co-variance_ (`A<+T>` or `A<*T>`) means that if `U` is a subtype of `V` then `A<U>` is a subtype of `A<V>`
- _contra-variance_ (`A<-T>`) means that if `U` is a subtype of `V` then `A<V>` is a subtype of `A<U>`
- _non-variance_ (`A<T>` or `A<!T>`)  means that if `U` is a different type than `V` then there is no subtyping relationship between `A<U>` and `A<V>`

_Cardinality preserving_ 
means that the cardinality of the type being defined never exceeds the cardinality of any of its type parameters.
For example `type T<X> = X -> bool`
is illegal and returns the error message `formal type parameter 'X' is not used according to its variance specification (it is used left of an arrow) (perhaps try declaring 'X' as '-X' or '!X')`
The type `X -> bool` has strictly more values than the type `X`. 
This affects certain uses of the type, so Dafny requires the declaration of `T` to explicitly say so. 
Marking the type parameter `X` with `-` or `!` announces that the cardinality of `T<X>` may by larger than that of `X`. 
If you use `-`, you’re also declaring `T` to be contravariant in its type argument, and if you use `!`, you’re declaring that `T` is non-variant in its type argument.

To fix it, we use the variance `!`:

    type T<!X> = X -> bool

This states that `T` does not preserve the cardinality of `X`, meaning there could be strictly more values of type `T<E>` than values of type `E` for any `E`.

A more detailed explanation of these topics is [here](http://leino.science/papers/krml280.html).

<!--PDF NEWPAGE-->
## 5.4. Generic Instantiation ([grammar](#g-generic-instantiation)) {#sec-generic-instantiation}

A generic instantiation consists of a comma-separated list of 1 or more Types,
enclosed in angle brackets (`<` `>`),
providing actual types to be used in place of the type parameters of the 
declaration of the generic type.
If there is no instantion for a generic type, type inference will try
to fill these in (cf. [Section 12.2](#sec-type-inference)).

<!--PDF NEWPAGE-->
## 5.5. Collection types {#sec-collection-types}

Dafny offers several built-in collection types.

### 5.5.1. Sets ([grammar](#g-collection-type)) {#sec-sets}

For any type `T`, each value of type `set<T>` is a finite set of
`T` values.

Set membership is determined by equality in the type `T`,
so `set<T>` can be used in a non-ghost context only if `T` is
[equality supporting](#sec-equality-supporting).

For any type `T`, each value of type `iset<T>` is a potentially infinite
set of `T` values.

A set can be formed using a [_set display_ expression](#sec-set-display-expression), which is a
possibly empty, unordered, duplicate-insensitive list of expressions
enclosed in curly braces.  To illustrate,
<!-- %no-check -->
```dafny
{}        {2, 7, 5, 3}        {4+2, 1+5, a*b}
```
are three examples of set displays. There is also a _set comprehension_
expression (with a binder, like in logical quantifications), described in
[Section 9.31.5](#sec-set-comprehension-expression).

In addition to equality and disequality, set types
support the following relational operations:

 operator        | precedence | description
-----------------|------------------------------------
 `<`             | 4 | proper subset
 `<=`            | 4 | subset
 `>=`            | 4 | superset
 `>`             | 4 | proper superset

Like the arithmetic relational operators, these operators are
chaining.

Sets support the following binary operators, listed in order of
increasing binding power:

 operator      | precedence | description
---------------|:---:|------------------------------------
 `!!`          | 4 | disjointness
---------------|------------------------------------
 `+`           | 6 | set union
 `-`           | 6 | set difference
---------------|------------------------------------
 `*`           | 7 |set intersection

The associativity rules of `+`, `-`, and `*` are like those of the
arithmetic operators with the same names.  The expression `A !! B`,
whose binding power is the same as equality (but which neither
associates nor chains with equality), says that sets `A` and `B` have
no elements in common, that is, it is equivalent to
<!-- %no-check -->
```dafny
A * B == {}
```
However, the disjointness operator is chaining though in a slightly different way than other chaining operators:
 `A !! B !! C !! D` means that `A`, `B`, `C` and `D` are all mutually disjoint, that is
<!-- %no-check -->
```dafny
A * B == {} && (A + B) * C == {} && (A + B + C) * D == {}
```

In addition, for any set `s` of type `set<T>` or `iset<T>` and any
expression `e` of type `T`, sets support the following operations:

 expression          | precedence | result type |  description
---------------------|:---:|:---:|------------------------------------
 `e in s`            | 4   | `bool` | set membership
 `e !in s`           | 3   | `bool` | set non-membership
 `|s|`               | 11  | `nat`  | set cardinality (not for `iset`)

The expression `e !in s` is a syntactic shorthand for `!(e in s)`.

(No white space is permitted between `!` and `in`, making `!in` effectively
the one example of a mixed-character-class token in Dafny.)

### 5.5.2. Multisets ([grammar](#g-collection-type)) {#sec-multisets}

A _multiset_ is similar to a set, but keeps track of the multiplicity
of each element, not just its presence or absence.  For any type `T`,
each value of type `multiset<T>` is a map from `T` values to natural
numbers denoting each element's multiplicity.  Multisets in Dafny
are finite, that is, they contain a finite number of each of a finite
set of elements.  Stated differently, a multiset maps only a finite
number of elements to non-zero (finite) multiplicities.

Like sets, multiset membership is determined by equality in the type
`T`, so `multiset<T>` can be used in a non-ghost context only if `T`
is [equality supporting](#sec-equality-supporting).

A multiset can be formed using a _multiset display_ expression, which
is a possibly empty, unordered list of expressions enclosed in curly
braces after the keyword `multiset`.  To illustrate,
<!-- %no-check -->
```dafny
multiset{}   multiset{0, 1, 1, 2, 3, 5}   multiset{4+2, 1+5, a*b}
```
are three examples of multiset displays.  There is no multiset
comprehension expression.

In addition to equality and disequality, multiset types
support the following relational operations:


 operator          | precedence | description
-------------------|-----------------------------------
  `<`              | 4 | proper multiset subset
  `<=`             | 4 | multiset subset
  `>=`             | 4 | multiset superset
  `>`              | 4 | proper multiset superset

Like the arithmetic relational operators, these operators are
chaining.

Multisets support the following binary operators, listed in order of
increasing binding power:

 operator      | precedence | description
---------------|:---:|------------------------------------
 `!!`          | 4 | multiset disjointness
---------------|------------------------------------
 `+`           | 6 |multiset sum
 `-`           | 6 |multiset difference
---------------|------------------------------------
 `*`           | 7 | multiset intersection

The associativity rules of `+`, `-`, and `*` are like those of the
arithmetic operators with the same names. The `+` operator
adds the multiplicity of corresponding elements, the `-` operator
subtracts them (but 0 is the minimum multiplicity),
and the `*` has multiplicity that is the minimum of the
multiplicity of the operands. There is no operator for multiset
union, which would compute the maximum of the multiplicities of the operands.

The expression `A !! B`
says that multisets `A` and `B` have no elements in common, that is,
it is equivalent to
<!-- %no-check -->
```dafny
A * B == multiset{}
```
Like the analogous set operator, `!!` is chaining and means mutual disjointness.

In addition, for any multiset `s` of type `multiset<T>`,
expression `e` of type `T`, and non-negative integer-based numeric
`n`, multisets support the following operations:

 expression      | precedence | result type      | description
-----------------|:---:|:----------------:|------------------------------------------
 `e in s`        | 4  |  `bool`         | multiset membership
 `e !in s`       | 4  |  `bool`         | multiset non-membership
 `|s|`           | 11 |   `nat`          | multiset cardinality
 `s[e]`          | 11 |  `nat`          | multiplicity of `e` in `s`
 `s[e := n]`     | 11 | `multiset<T>`    | multiset update (change of multiplicity)

The expression `e in s` returns `true` if and only if `s[e] != 0`.
The expression `e !in s` is a syntactic shorthand for `!(e in s)`.
The expression `s[e := n]` denotes a multiset like
`s`, but where the multiplicity of element `e` is `n`.  Note that
the multiset update `s[e := 0]` results in a multiset like `s` but
without any occurrences of `e` (whether or not `s` has occurrences of
`e` in the first place).  As another example, note that
`s - multiset{e}` is equivalent to:
<!-- %no-check -->
```dafny
if e in s then s[e := s[e] - 1] else s
```

### 5.5.3. Sequences ([grammar](#g-collection-type)) {#sec-sequences}

For any type `T`, a value of type `seq<T>` denotes a _sequence_ of `T`
elements, that is, a mapping from a finite downward-closed set of natural
numbers (called _indices_) to `T` values.

#### 5.5.3.1. Sequence Displays {#sec-sequence-displays}
A sequence can be formed using a _sequence display_ expression, which
is a possibly empty, ordered list of expressions enclosed in square
brackets.  To illustrate,
<!-- %no-check -->
```dafny
[]        [3, 1, 4, 1, 5, 9, 3]        [4+2, 1+5, a*b]
```
are three examples of sequence displays.

  There is also a sequence
comprehension expression ([Section 9.28](#sec-seq-comprehension)):
<!-- %no-check -->
```dafny
seq(5, i => i*i)
```
is equivalent to `[0, 1, 4, 9, 16]`.

#### 5.5.3.2. Sequence Relational Operators
In addition to equality and disequality, sequence types
support the following relational operations:

 operator        | precedence | description
-----------------|------------------------------------
  <              | 4 | proper prefix
  <=             | 4 | prefix

Like the arithmetic relational operators, these operators are
chaining.  Note the absence of `>` and `>=`.

#### 5.5.3.3. Sequence Concatenation
Sequences support the following binary operator:

 operator      | precedence | description
---------------|------------------------------------
 `+`           | 6 | concatenation

Operator `+` is associative, like the arithmetic operator with the
same name.

#### 5.5.3.4. Other Sequence Expressions {#sec-other-sequence-expressions}
In addition, for any sequence `s` of type `seq<T>`, expression `e`
of type `T`, integer-based numeric `i` satisfying `0 <= i < |s|`, and
integer-based numerics `lo` and `hi` satisfying
`0 <= lo <= hi <= |s|`, sequences support the following operations:

 expression         | precedence | result type | description
 -------------------|:---:|:---:|----------------------------------------
 `e in s`           | 4 | `bool` | sequence membership
 `e !in s`          | 4 | `bool` | sequence non-membership
 `|s|`              | 11 | `nat` | sequence length
 `s[i]`             | 11 | `T` | sequence selection
 `s[i := e]`        | 11 | `seq<T>` | sequence update
 `s[lo..hi]`        | 11 | `seq<T>`| subsequence
 `s[lo..]`          | 11 | `seq<T>` | drop
 `s[..hi]`          | 11 | `seq<T>` | take
 `s[`_slices_`]`    | 11 | `seq<seq<T>>` | slice
 `multiset(s)`      | 11 | `multiset<T>`| sequence conversion to a `multiset<T>`

Expression `s[i := e]` returns a sequence like `s`, except that the
element at index `i` is `e`.  The expression `e in s` says there
exists an index `i` such that `s[i] == e`.  It is allowed in non-ghost
contexts only if the element type `T` is
[equality supporting](#sec-equality-supporting).
The expression `e !in s` is a syntactic shorthand for `!(e in s)`.

Expression `s[lo..hi]` yields a sequence formed by taking the first
`hi` elements and then dropping the first `lo` elements.  The
resulting sequence thus has length `hi - lo`.  Note that `s[0..|s|]`
equals `s`.  If the upper bound is omitted, it
defaults to `|s|`, so `s[lo..]` yields the sequence formed by dropping
the first `lo` elements of `s`.  If the lower bound is omitted, it
defaults to `0`, so `s[..hi]` yields the sequence formed by taking the
first `hi` elements of `s`.

In the sequence slice operation, _slices_ is a nonempty list of
length designators separated and optionally terminated by a colon, and
there is at least one colon.  Each length designator is a non-negative
integer-based numeric; the sum of the length designators is no greater than `|s|`.  If there
are _k_ colons, the operation produces _k + 1_ consecutive subsequences
from `s`, with the length of each indicated by the corresponding length
designator, and returns these as a sequence of
sequences.
If _slices_ is terminated by a
colon, then the length of the last slice extends until the end of `s`,
that is, its length is `|s|` minus the sum of the given length
designators.  For example, the following equalities hold, for any
sequence `s` of length at least `10`:
<!-- %check-verify -->
```dafny
method m(s: seq<int>) {
  var t := [3.14, 2.7, 1.41, 1985.44, 100.0, 37.2][1:0:3];
  assert |t| == 3 && t[0] == [3.14] && t[1] == [];
  assert t[2] == [2.7, 1.41, 1985.44];
  var u := [true, false, false, true][1:1:];
  assert |u| == 3 && u[0][0] && !u[1][0] && u[2] == [false, true];
  assume |s| > 10;
  assert s[10:][0] == s[..10];
  assert s[10:][1] == s[10..];
}
```

The operation `multiset(s)` yields the multiset of elements of
sequence `s`.  It is allowed in non-ghost contexts only if the element
type `T` is [equality supporting](#sec-equality-supporting).

#### 5.5.3.5. Strings ([grammar](#g-collection-type)) {#sec-strings}

A special case of a sequence type is `seq<char>`, for which Dafny
provides a synonym: `string`.  Strings are like other sequences, but
provide additional syntax for sequence display expressions, namely
_string literals_.  There are two forms of the syntax for string
literals:  the _standard form_ and the _verbatim form_.

String literals of the standard form are enclosed in double quotes, as
in `"Dafny"`.  To include a double quote in such a string literal,
it is necessary to use an escape sequence.  Escape sequences can also
be used to include other characters.  The supported escape sequences
are the same as those for character literals ([Section 5.2.5](#sec-characters)).
For example, the Dafny expression `"say \"yes\""` represents the
string `'say "yes"'`.
The escape sequence for a single quote is redundant, because
`"\'"` and `"\'"` denote the same
string---both forms are provided in order to support the same
escape sequences as do character literals.

String literals of the verbatim form are bracketed by
`@"` and `"`, as in `@"Dafny"`.  To include
a double quote in such a string literal, it is necessary to use the
escape sequence `""`, that is, to write the character
twice.  In the verbatim form, there are no other escape sequences.
Even characters like newline can be written inside the string literal
(hence spanning more than one line in the program text).

For example, the following three expressions denote the same string:
<!-- %no-check -->
```dafny
"C:\\tmp.txt"
@"C:\tmp.txt"
['C', ':', '\\', 't', 'm', 'p', '.', 't', 'x', 't']
```

Since strings are sequences, the relational operators `<`
and `<=` are defined on them.  Note, however, that these operators
still denote proper prefix and prefix, respectively, not some kind of
alphabetic comparison as might be desirable, for example, when
sorting strings.

### 5.5.4. Finite and Infinite Maps ([grammar](#g-collection-type)) {#sec-maps}

For any types `T` and `U`, a value of type `map<T,U>` denotes a
_(finite) map_
from `T` to `U`.  In other words, it is a look-up table indexed by
`T`.  The _domain_ of the map is a finite set of `T` values that have
associated `U` values.  Since the keys in the domain are compared
using equality in the type `T`, type `map<T,U>` can be used in a
non-ghost context only if `T` is
[equality supporting](#sec-equality-supporting).

Similarly, for any types `T` and `U`, a value of type `imap<T,U>`
denotes a _(possibly) infinite map_.  In most regards, `imap<T,U>` is
like `map<T,U>`, but a map of type `imap<T,U>` is allowed to have an
infinite domain.

A map can be formed using a _map display_ expression (see [Section 0.0.0](#sec-map-display-expression)),
which is a possibly empty, ordered list of _maplets_, each maplet having the
form `t := u` where `t` is an expression of type `T` and `u` is an
expression of type `U`, enclosed in square brackets after the keyword
`map`.  To illustrate,
<!-- %no-check -->
```dafny
map[]
map[20 := true, 3 := false, 20 := false]
map[a+b := c+d]
```
are three examples of map displays.  By using the keyword `imap`
instead of `map`, the map produced will be of type `imap<T,U>`
instead of `map<T,U>`.  Note that an infinite map (`imap`) is allowed
to have a finite domain, whereas a finite map (`map`) is not allowed
to have an infinite domain.
If the same key occurs more than
once in a map display expression, only the last occurrence appears in the resulting
map.[^fn-map-display]  There is also a _map comprehension expression_,
explained in [Section 9.31.8](#sec-map-comprehension-expression).

[^fn-map-display]: This is likely to change in the future to disallow
    multiple occurrences of the same key.

For any map `fm` of type `map<T,U>`,
any map `m` of type `map<T,U>` or `imap<T,U>`,
any expression `t` of type `T`,
any expression `u` of type `U`, and any `d` in the domain of `m` (that
is, satisfying `d in m`), maps support the following operations:

 expression     | precedence | result type | description
 ---------------|:---:|:-----------:|------------------------------------
 `t in m`       | 4 | `bool`      | map domain membership
 `t !in m`      | 4 | `bool`      | map domain non-membership
 `|fm|`         | 11 | `nat`       | map cardinality
 `m[d]`         | 11 | `U`         | map selection
 `m[t := u]`    | 11 | `map<T,U>`  | map update
 `m.Keys`      | 11 | (i)`set<T>`    | the domain of `m`
 `m.Values`    | 11 | (i)`set<U>`    | the range of `m`
 `m.Items`     | 11 | (i)`set<(T,U)>`| set of pairs (t,u) in `m`

`|fm|` denotes the number of mappings in `fm`, that is, the
cardinality of the domain of `fm`.  Note that the cardinality operator
is not supported for infinite maps.
Expression `m[d]` returns the `U` value that `m` associates with `d`.
Expression `m[t := u]` is a map like `m`, except that the
element at key `t` is `u`.  The expression `t in m` says `t` is in the
domain of `m` and `t !in m` is a syntactic shorthand for
`!(t in m)`.[^fn-map-membership]

The expressions `m.Keys`, `m.Values`, and `m.Items` return, as sets,
the domain, the range, and the 2-tuples holding the key-value
associations in the map. Note that `m.Values` will have a different
cardinality than `m.Keys` and `m.Items` if different keys are
associated with the same value. If `m` is an `imap`, then these
expressions return `iset` values.

[^fn-map-membership]: This is likely to change in the future as
    follows:  The `in` and `!in` operations will no longer be
    supported on maps, with `x in m` replaced by `x in m.Keys`,
and similarly for `!in`.

Here is a small example, where a map `cache` of type `map<int,real>`
is used to cache computed values of Joule-Thomson coefficients for
some fixed gas at a given temperature:
<!-- %no-check -->
```dafny
if K in cache {  // check if temperature is in domain of cache
  coeff := cache[K];  // read result in cache
} else {
  coeff := ComputeJTCoefficient(K); // do expensive computation
  cache := cache[K := coeff];  // update the cache
}
```

Dafny also overloads the `+` and `-` binary operators for maps.
The `+` operator merges two maps or imaps of the same type, as if each
(key,value) pair of the RHS is added in turn to the LHS (i)map.
In this use, `+` is not commutative; if a key exists in both
(i)maps, it is the value from the RHS (i)map that is present in the result.

The `-` operator implements a map difference operator. Here the LHS
is a `map<K,V>` or `imap<K,V>` and the RHS is a `set<K>` (but not an `iset`); the operation removes
from the LHS all the (key,value) pairs whose key is a member of the RHS set.

### 5.5.5. Iterating over collections

Collections are very commonly used in programming and one frequently
needs to iterate over the elements of a collection. Dafny does not have
built-in iterator methods, but the idioms by which to do so are straightforward.
The subsections below give some introductory examples; more
detail can be found in this [power user note](http://leino.science/papers/krml275.html).

#### 5.5.5.1. Sequences and arrays

Sequences and arrays are indexable and have a length. So the idiom to
iterate over the contents is well-known. For an array:
<!-- %check-resolve -->
```dafny
method m(a: array<int>) {
  var i := 0;
  var sum := 0;
  while i < a.Length {
    sum := sum + a[i];
    i := i + 1;
  }
}
```
For a sequence, the only difference is the length operator:
<!-- %check-resolve -->
```dafny
method m(s: seq<int>) {
  var i := 0;
  var sum := 0;
  while i < |s| {
    sum := sum + s[i];
    i := i + 1;
  }
}
```

The `forall` statement ([Section 8.21](#sec-forall-statement)) can also be used
with arrays where parallel assignment is needed:
<!-- %check-resolve -->
```dafny
method m(s: array<int>) {
  var rev := new int[s.Length];
  forall i | 0 <= i < s.Length {
    rev[i] := s[s.Length-i-1];
  }
}
```

See [Section 5.10.2](#sec-array-to-seq) on how to convert an array to a sequence.

#### 5.5.5.2. Sets
There is no intrinsic order to the elements of a set. Nevertheless, we can
extract an arbitrary element of a nonempty set, performing an iteration
as follows:
<!-- %check-resolve -->
```dafny
method m(s: set<int>) {
  var ss := s;
  while ss != {}
    decreases |ss|
  {
    var i: int :| i in ss;
    ss := ss - {i};
    print i, "\n";
  }
}
```

Because `iset`s may be infinite, Dafny does not permit iteration over an `iset`.

#### 5.5.5.3. Maps

Iterating over the contents of a `map` uses the component sets: `Keys`, `Values`, and `Items`. The iteration loop follows the same patterns as for sets:

<!-- %check-resolve -->
```dafny
method m<T(==),U(==)> (m: map<T,U>) {
  var items := m.Items;
  while items != {}
    decreases |items|
  {
    var item :| item in items;
    items := items - { item };
    print item.0, " ", item.1, "\n";
  }
}
```

There are no mechanisms currently defined in Dafny for iterating over `imap`s.


<!--PDF NEWPAGE-->
## 5.6. Types that stand for other types ([grammar](#g-type-definition)) {#sec-type-definition}

It is sometimes useful to know a type by several names or to treat a
type abstractly. There are several mechanisms in Dafny to do this:

* ([Section 5.6.1](#sec-synonym-type)) A typical _synonym type_, in which a type name is a synonym for another type
* ([Section 5.6.2](#sec-opaque-types)) An _opaque type_, in which a new type name is declared as an uninterpreted type
* ([Section 5.6.3](#sec-subset-types)) A _subset type_, in which a new type name is given to a subset of the values of a given type
* ([Section 0.0){#sec-newtypes)) A _newtype_, in which a subset type is declared, but with restrictions on converting to and from its base type

### 5.6.1. Type synonyms ([grammar](#g-type-definition)) {#sec-synonym-type}

<!-- %check-resolve -->
```dafny
type T = int
type SS<T> = set<set<T>>
```

A _type synonym_ declaration:
<!-- %no-check -->
```dafny
type Y<T> = G
```
declares `Y<T>` to be a synonym for the type `G`.
If the `= G` is omitted then the declaration just declares a name as an uninterpreted
_opaque_ type, as described in [Section 5.6.2](#sec-opaque-types).  Such types may be
given a definition elsewhere in the Dafny program.

  Here, `T` is a
nonempty list of type parameters (each of which optionally
has a [type characteristics suffix](#sec-type-characteristics)), which can be used as free type
variables in `G`.  If the synonym has no type parameters, the "`<T>`"
is dropped.  In all cases, a type synonym is just a synonym.  That is,
there is never a difference, other than possibly in error messages
produced, between `Y<T>` and `G`.

For example, the names of the following type synonyms may improve the
readability of a program:
<!-- %check-resolve -->
```dafny
type Replacements<T> = map<T,T>
type Vertex = int
```

The new type name itself may have type characteristics declared, though these are typically
inferred from the definition, if there is one.

As already described in [Section 5.5.3.5](#sec-strings), `string` is a built-in
type synonym for `seq<char>`, as if it would have been declared as
follows:
<!-- %check-resolve -->
```dafny
type string_(==,0,!new) = seq<char>
```
If the implicit declaration did not include the type characteristics, they would be inferred in any case.

### 5.6.2. Opaque types ([grammar](#g-type-definition)) {#sec-opaque-types}

Examples:
<!-- %check-resolve -->
```dafny
type T
type Q { function method toString(t: T): string }
```

An opaque type is a special case of a type synonym that is underspecified.  Such
a type is declared simply by:
<!-- %check-resolve -->
```dafny
type Y<T>
```
Its definition can be stated in a
refining module.  The name `Y` can be immediately followed by
a type characteristics suffix ([Section 5.3.1](#sec-type-characteristics)).
Because there is no defining RHS, the type characteristics cannot be inferred and so
must be stated. If, in some refining module, a definition of the type is given, the
type characteristics must match those of the new definition.

For example, the declarations
<!-- %check-resolve -->
```dafny
type T
function F(t: T): T
```
can be used to model an uninterpreted function `F` on some
arbitrary type `T`.  As another example,
<!-- %check-resolve -->
```dafny
type Monad<T>
```
can be used abstractly to represent an arbitrary parameterized monad.

Even as an opaque type, the type
may be given members such as constants, methods or functions.
For example,
<!-- %check-resolve -->
```dafny
abstract module P {
  type T {
    function ToString(): string
  }
}

module X refines P {
  newtype T = i | 0 <= i < 10 {
    function ToString(): string {  "" }
  }
}
```
The abstract type `P.T` has a declared member `ToString`, which can be called wherever `P.T` may be used.
In the refining module `X`, `T` is declared to be a `newtype`, in which `ToString` now has a body.

It would be an error to refine `P.T` as a simple type synonym or subset type in `X`, say `type T = int`, because
type synonyms may not have members.

### 5.6.3. Subset types ([grammar](#g-type-definition)) {#sec-subset-types}

Examples:
<!-- %check-resolve -->
```dafny
type Pos = i: int | i > 0 witness 1
type PosReal = r | r > 0.0 witness 1.0
type Empty = n: nat | n < 0 witness *
type Big = n: nat | n > 1000 ghost witness 10000
```

A _subset type_ is a restricted use of an existing type, called
the _base type_ of the subset type.  A subset type is like a
combined use of the base type and a predicate on the base
type.

An assignment from a subset type to its base type is always
allowed.  An assignment in the other direction, from the base type to
a subset type, is allowed provided the value assigned does indeed
satisfy the predicate of the subset type. This condition is checked
by the verifier, not by the type checker. Similarly, assignments from
one subset type to another (both with the same base type) are also
permitted, as long as it can be established that the value being assigned
satisfies the predicate defining the receiving subset type.
(Note, in contrast, assignments between a newtype and its base type
are never allowed, even if the value assigned is a value of the target
type.  For such assignments, an explicit conversion must be used, see
[Section 9.10](#sec-as-is-expression).)

The declaration of a subset type permits an optional [`witness` clause](#sec-witness), to declare default values that the compiler can use to initialize variables of the subset type, or to assert the non-emptiness of the subset type.

Dafny builds in three families of subset types, as described next.

#### 5.6.3.1. Type `nat`

The built-in type `nat`, which represents the non-negative integers
(that is, the natural numbers), is a subset type:
<!-- %no-check -->
```dafny
type nat = n: int | 0 <= n
```

A simple example that
puts subset type `nat` to good use is the standard Fibonacci
function:
<!-- %check-verify -->
```dafny
function Fib(n: nat): nat
{
  if n < 2 then n else Fib(n-2) + Fib(n-1)
}
```
An equivalent, but clumsy, formulation of this function (modulo the
wording of any error messages produced at call sites) would be to use
type `int` and to write the restricting predicate in pre- and
postconditions:
<!-- %check-verify -->
```dafny
function Fib(n: int): int
  requires 0 <= n  // the function argument must be non-negative
  ensures 0 <= Fib(n)  // the function result is non-negative
{
  if n < 2 then n else Fib(n - 2) + Fib(n - 1)
}
```

#### 5.6.3.2. Non-null types

Every class, trait, and iterator declaration `C` gives rise to two types.

One type has the name `C?` (that is, the name of the class, trait,
or iterator declaration with a `?` character appended to the end).
The values of `C?` are the references to `C` objects, and also
the value `null`.
In other words, `C?` is the type of _possibly null_ references
(aka, _nullable_ references) to `C` objects.

The other type has the name `C` (that is, the same name as the
class, trait, or iterator declaration).
Its values are the references to `C` objects, and does not contain
the value `null`.
In other words, `C` is the type of _non-null_ references to `C`
objects.

The type `C` is a subset type of `C?`:
<!-- %no-check -->
```dafny
type C = c: C? | c != null
```
(It may be natural to think of the type `C?` as the union of
type `C` and the value `null`, but, technically, Dafny defines
`C` as a subset type with base type `C?`.)

From being a subset type, we get that `C` is a subtype of `C?`.
Moreover, if a class or trait `C` extends a trait `B`, then
type `C` is a subtype of `B` and type `C?` is a subtype of `B?`.

Every possibly-null reference type is a subtype of the
built-in possibly-null trait type `object?`, and
every non-null reference type is a subtype of the
built-in non-null trait type `object`. (And, from the fact
that `object` is a subset type of `object?`, we also have that
`object` is a subtype of `object?`.)

Arrays are references and array types also come in these two flavors.
For example,
`array?` and `array2?` are possibly-null (1- and 2-dimensional) array types, and
`array` and `array2` are their respective non-null types.

Note that `?` is not an operator. Instead, it is simply the last
character of the name of these various possibly-null types.

#### 5.6.3.3. Arrow types: `->`, `-->`, and `~>` {#sec-arrow-subset-types}

For more information about arrow types (function types), see [Section 5.12](#sec-arrow-types).
This section is a preview to point out the subset-type relationships among the kinds
of function types.

The built-in type 

- `->` stands for total functions, 
- `-->` stands for partial functions (that is, functions with possible `requires` clauses),
and 
- `~>` stands for all functions. 

More precisely, type constructors
exist for any arity (`() -> X`, `A -> X`, `(A, B) -> X`, `(A, B, C) -> X`,
etc.).

For a list of types `TT` and a type `U`, the values of the arrow type `(TT) ~> U`
are functions from `TT` to `U`. This includes functions that may read the
heap and functions that are not defined on all inputs. It is not common
to need this generality (and working with such general functions is
difficult). Therefore, Dafny defines two subset types that are more common
(and much easier to work with).

The type `(TT) --> U` denotes the subset of `(TT) ~> U` where the functions
do not read the (mutable parts of the) heap.
Values of type `(TT) --> U` are called _partial functions_,
and the subset type `(TT) --> U` is called the _partial arrow type_.
(As a mnemonic to help you remember that this is the partial arrow, you may
think of the little gap between the two hyphens in `-->` as showing a broken
arrow.)

The built-in partial arrow type is defined as follows (here shown
for arrows with arity 1):
<!-- %no-check -->
```dafny
type A --> B = f: A ~> B | forall a :: f.reads(a) == {}
```
(except that what is shown here left of the `=` is not legal Dafny syntax).
That is, the partial arrow type is defined as those functions `f`
whose reads frame is empty for all inputs.
More precisely, taking variance into account, the partial arrow type
is defined as
<!-- %no-check -->
```dafny
type -A --> +B = f: A ~> B | forall a :: f.reads(a) == {}
```

The type `(TT) -> U` is, in turn, a subset type of `(TT) --> U`, adding the
restriction that the functions must not impose any precondition. That is,
values of type `(TT) -> U` are _total functions_, and the subset type
`(TT) -> U` is called the _total arrow type_.

The built-in total arrow type is defined as follows (here shown
for arrows with arity 1):
<!-- %no-check -->
```dafny
type -A -> +B = f: A --> B | forall a :: f.requires(a)
```
That is, the total arrow type is defined as those partial functions `f`
whose precondition evaluates to `true` for all inputs.

Among these types, the most commonly used are the total arrow types.
They are also the easiest to work with. Because they are common, they
have the simplest syntax (`->`).

Note, informally, we tend to speak of all three of these types as arrow types,
even though, technically, the `~>` types are the arrow types and the
`-->` and `->` types are subset types thereof. The one place where you may need to
remember that `-->` and `->` are subset types is in some error messages.
For example, if you try to assign a partial function to a variable whose
type is a total arrow type and the verifier is not able to prove that the
partial function really is total, then you'll get an error saying that the subset-type
constraint may not be satisfied.


#### 5.6.3.4. Witness clauses {#sec-witness}

The declaration of a subset type permits an optional `witness` clause.
Types in Dafny are generally expected to be non-empty, in part because
variables of any type are expected to have some value when they are used.
In many cases, Dafny can determine that a newly declared type has 
some value. For example, a numeric type that includes 0 is known by Dafny
to be non-empty. However, Dafny cannot always make this determination.
If it cannot, a `witness` clause is required. The value given in
the `witness` clause must be a valid value for the type and assures Dafny
that the type is non-empty.

For example, 
<!-- %check-verify Types.10.expect -->
```dafny
type OddInt = x: int | x % 2 == 1
```
will give an error message, but
<!-- %check-verify -->
```dafny
type OddInt = x: int | x % 2 == 1 witness 73
```
does not. Here is another example:
<!-- %check-verify -->
```dafny
type NonEmptySeq = x: seq<int> | |x| > 0 witness [0]
```

If the witness is only available in ghost code, you can declare the witness
as a `ghost witness`. In this case, the Dafny verifier knows that the type
is non-empty, but it will not be able to auto-initialize a variable of that
type in compiled code.

There is even room to do the following:
<!-- %check-verify -->
```dafny
type BaseType
predicate RHS(x: BaseType)
type MySubset = x: BaseType | RHS(x) ghost witness MySubsetWitness()

function MySubsetWitness(): BaseType
  ensures RHS(MySubsetWitness())
```
Here the type is given a ghost witness: the result of the expression
`MySubsetWitness()`, which is a call of a (ghost) function.
Now that function has a postcondition saying that the returned value 
is indeed a candidate value for the declared type, so the verifier is
satisfied regarding the non-emptiness of the type. However, the function
has no body, so there is still no proof that there is indeed such a witness.
You can either supply a, perhaps complicated, body to generate a viable
candidate or you can be very sure, without proof, that there is indeed such a value.
If you are wrong, you have introduced an unsoundness into your program.

In addition though, types are allowed to be empty or possibly empty.
This is indicated by the clause `witness *`, which tells the verifier not to check for a satisfying witness.
A declaration like this produces an empty type:
<!-- %check-verify -->
```dafny
type ReallyEmpty = x: int | false witness *
``` <!-- %save ReallyEmpty.tmp -->
The type can be used in code like
<!-- %check-verify %use ReallyEmpty.tmp -->
```dafny
method M(x: ReallyEmpty) returns (seven: int)
  ensures seven == 7
{
  seven := 10;
}
```
which does verify. But the method can never be called because there is no value that
can be supplied as the argument. Even this code
<!-- %check-verify Types.10a.expect %use ReallyEmpty.tmp -->
```dafny
method P() returns (seven: int)
  ensures seven == 7
{
  var x: ReallyEmpty;
  seven := 10;
}
```
does not complain about `x` unless `x` is actually used, in which case it must have a value.
The postcondition in `P` does not verify, but not because of the empty type.

<!--PDF NEWPAGE-->
## 5.7. Newtypes ([grammar](#g-type-definition)) {#sec-newtypes}

Examples:
<!-- %check-resolve -->
```dafny
newtype I = int
newtype D = i: int | 0 <= i < 10
newtype uint8 = i | 0 <= i < 256
```

A newtype is like a type synonym or subset type except that it declares a wholly new type
name that is distinct from its base type. It also accepts an optional [`witness` clause](#sec-witness).

A new type can be declared with the _newtype_
declaration, for example:
<!-- %no-check -->
```dafny
newtype N = x: M | Q
```
where `M` is a type and `Q` is a boolean expression that can
use `x` as a free variable.  If `M` is an integer-based numeric type,
then so is `N`; if `M` is real-based, then so is `N`.  If the type `M`
can be inferred from `Q`, the "`: M`" can be omitted.  If `Q` is just
`true`, then the declaration can be given simply as:
<!-- %no-check -->
```dafny
newtype N = M
```
Type `M` is known as the _base type_ of `N`. At present, Dafny only supports
`int` and `real` as base types of newtypes.

A newtype is a type that supports the same operations as its
base type.  The newtype is distinct from and incompatible with other
types; in particular, it is not assignable to its base type
without an explicit conversion.  An important difference between the
operations on a newtype and the operations on its base type is that
the newtype operations are defined only if the result satisfies the
predicate `Q`, and likewise for the literals of the
newtype.

For example, suppose `lo` and `hi` are integer-based numerics that
satisfy `0 <= lo <= hi` and consider the following code fragment:
<!-- %no-check -->
```dafny
var mid := (lo + hi) / 2;
```
If `lo` and `hi` have type `int`, then the code fragment is legal; in
particular, it never overflows, since `int` has no upper bound.  In
contrast, if `lo` and `hi` are variables of a newtype `int32` declared
as follows:
<!-- %check-verify -->
```dafny
newtype int32 = x | -0x8000_0000 <= x < 0x8000_0000
```
then the code fragment is erroneous, since the result of the addition
may fail to satisfy the predicate in the definition of `int32`.  The
code fragment can be rewritten as
<!-- %no-check -->
```dafny
var mid := lo + (hi - lo) / 2;
```
in which case it is legal for both `int` and `int32`.

Since a newtype is incompatible with its base type and since all
results of the newtype's operations are members of the newtype, a
compiler for Dafny is free to specialize the run-time representation
of the newtype.  For example, by scrutinizing the definition of
`int32` above, a compiler may decide to store `int32` values using
signed 32-bit integers in the target hardware.

The incompatibility of a newtype and its basetype is intentional,
as newtypes are meant to be used as distinct types from the basetype.
If numeric types are desired that mix more readily with the basetype,
the subset types described in [Section 5.6.3](#sec-subset-types)
 may be more appropriate.

Note that the bound variable `x` in `Q` has type `M`, not `N`.
Consequently, it may not be possible to state `Q` about the `N`
value.  For example, consider the following type of 8-bit 2's
complement integers:
<!-- %check-verify -->
```dafny
newtype int8 = x: int | -128 <= x < 128
```
and consider a variable `c` of type `int8`.  The expression
<!-- %no-check -->
```dafny
-128 <= c < 128
```
is not well-defined, because the comparisons require each operand to
have type `int8`, which means the literal `128` is checked to be of
type `int8`, which it is not.  A proper way to write this expression
is to use a conversion operation, described in [Section 5.7.1](#sec-conversion), on `c` to
convert it to the base type:
<!-- %no-check -->
```dafny
-128 <= c as int < 128
```

If possible, Dafny compilers will represent values of the newtype using
a native type for the sake of efficiency. This action can
be inhibited or a specific native data type selected by
using the `{:nativeType}` attribute, as explained in
[Section 11.1.2](#sec-nativetype).

Furthermore, for the compiler to be able to make an appropriate choice of
representation, the constants in the defining expression as shown above must be
known constants at compile-time. They need not be numeric literals; combinations
of basic operations and symbolic constants are also allowed as described
in [Section 9.38](#sec-compile-time-constants).

### 5.7.1. Conversion operations {#sec-conversion}

For every type `N`, there is a conversion operation with the
name `as N`, described more fully in [Section 9.10](#sec-as-is-expression).
It is a partial function defined when the
given value, which can be of any type, is a member of the type
converted to.  When the conversion is from a real-based numeric type
to an integer-based numeric type, the operation requires that the
real-based argument have no fractional part.  (To round a real-based
numeric value down to the nearest integer, use the `.Floor` member,
see [Section 5.2.2](#sec-numeric-types).)

To illustrate using the example from above, if `lo` and `hi` have type
`int32`, then the code fragment can legally be written as follows:
<!-- %no-check -->
```dafny
var mid := (lo as int + hi as int) / 2;
```
where the type of `mid` is inferred to be `int`.  Since the result
value of the division is a member of type `int32`, one can introduce
yet another conversion operation to make the type of `mid` be `int32`:
<!-- %no-check -->
```dafny
var mid := ((lo as int + hi as int) / 2) as int32;
```
If the compiler does specialize the run-time representation for
`int32`, then these statements come at the expense of two,
respectively three, run-time conversions.

The `as N` conversion operation is grammatically a suffix operation like
`.`field and array indexing, but binds less tightly than unary operations:
`- x as int` is `(- x) as int`; `a + b as int` is `a + (b as int)`.

The `as N` conversion can also be used with reference types. For example,
if `C` is a class, `c` is an expression of type `C`, and `o` is an expression
of type `object`, then `c as object` and `c as object?` are upcasts
and `o is C` is a downcast. A downcast requires the LHS expression to
have the RHS type, as is enforced by the verifier.

For some types (in particular, reference types), there is also a
corresponding `is` operation ([Section 9.10](#sec-as-is-expression)) that
tests whether a value is valid for a given type.

<!--PDF NEWPAGE-->
## 5.8. Class types ([grammar](#g-class-type)) {#sec-class-types}

Examples:
<!-- %check-resolve -->
```dafny
trait T {}
class A {}
class B extends T {
  const b: B?
  var v: int
  constructor (vv: int) { v := vv; b := null; }
  function toString(): string { "a B" }
  method m(i: int) { var x := new B(0); }
  static method q() {}
}
```

Declarations within a class all begin with keywords and do not end with semicolons.



A _class_ `C` is a reference type declared as follows:
<!-- %no-check -->
```dafny
class C<T> extends J1, ..., Jn
{
  _members_
}
```
where the <>-enclosed list of one-or-more type parameters `T` is optional. The text
"`extends J1, ..., Jn`" is also optional and says that the class extends traits `J1` ... `Jn`.
The members of a class are _fields_, _constant fields_, _functions_, and
_methods_.  These are accessed or invoked by dereferencing a reference
to a `C` instance.

A function or method is invoked on an _instance_
of `C`, unless the function or method is declared `static`.
A function or method that is not `static` is called an
_instance_ function or method.

An instance function or method takes an implicit _receiver_
parameter, namely, the instance used to access the member.  In the
specification and body of an instance function or method, the receiver
parameter can be referred to explicitly by the keyword `this`.
However, in such places, members of `this` can also be mentioned
without any qualification.  To illustrate, the qualified `this.f` and
the unqualified `f` refer to the same field of the same object in the
following example:
<!-- %check-resolve -->
```dafny
class C {
  var f: int
  var x: int
  method Example() returns (b: bool)
  {
    var x: int;
    b := f == this.f;
  }
}
```
so the method body always assigns `true` to the out-parameter `b`.
However, in this example, `x` and `this.x` are different because
the field `x` is shadowed by the declaration of the local variable `x`.
There is no semantic difference between qualified and
unqualified accesses to the same receiver and member.

A `C` instance is created using `new`. There are three forms of `new`,
depending on whether or not the class declares any _constructors_
(see [Section 6.3.2](#sec-constructor-methods)):

<!-- %no-check -->
```dafny
c := new C;
c := new C.Init(args);
c := new C(args);
```

For a class with no constructors, the first two forms can be used.
The first form simply allocates a new instance of a `C` object, initializing
its fields to values of their respective types (and initializing each `const` field
with a RHS to its specified value). The second form additionally invokes
an _initialization method_ (here, named `Init`) on the newly allocated object
and the given arguments. It is therefore a shorthand for
<!-- %no-check -->
```dafny
c := new C;
c.Init(args);
```
An initialization method is an ordinary method that has no out-parameters and
that modifies no more than `this`.

For a class that declares one or more constructors, the second and third forms
of `new` can be used. For such a class, the second form invokes the indicated
constructor (here, named `Init`), which allocates and initializes the object.
The third form is the same as the second, but invokes the _anonymous constructor_
of the class (that is, a constructor declared with the empty-string name).


<!--PDF NEWPAGE-->
## 5.9. Trait types ([grammar](#g-trait-type)) {#sec-trait-types}

A _trait_ is an abstract superclass, similar to an "interface" or
"mixin". A trait can be _extended_ only by another trait or
by a class (and in the latter case we say that the class _implements_
the trait). More specifically, algebraic datatypes cannot extend traits.[^fn-traits]

[^fn-traits]: Traits are new to Dafny and are likely to evolve for a while.

The declaration of a trait is much like that of a class:
<!-- %no-check -->
```dafny
trait J
{
  _members_
}
```
where _members_ can include fields, constant fields, functions, methods and declarations of nested traits, but
no constructor methods.  The functions and methods are allowed to be
declared `static`.

A reference type `C` that extends a trait `J` is assignable to a variable of
type `J`;
a value of type `J` is assignable to a variable of a reference type `C` that
extends `J` only if the verifier can prove that the reference does
indeed refer to an object of allocated type `C`.
The members of `J` are available as members
of `C`.  A member in `J` is not allowed to be redeclared in `C`,
except if the member is a non-`static` function or method without a
body in `J`.  By doing so, type `C` can supply a stronger
specification and a body for the member. There is further discussion on
this point in [Section 5.9.2](#sec-inheritance).

`new` is not allowed to be used with traits.  Therefore, there is no
object whose allocated type is a trait.  But there can of course be
objects of a class `C` that implement a trait `J`, and a reference to
such a `C` object can be used as a value of type `J`.

### 5.9.1. Type `object` ([grammar](#g-object-type)) {#sec-object-type}

There is a built-in trait `object` that is implicitly extended by all classes and traits.
It produces two types: the type `object?` that is a supertype of all
reference types and a subset type `object` that is a supertype of all non-null reference types.
This includes reference types like arrays and iterators that do not permit
explicit extending of traits. The purpose of type `object`
is to enable a uniform treatment of _dynamic frames_. In particular, it
is useful to keep a ghost field (typically named `Repr` for
"representation") of type `set<object>`.

It serves no purpose (but does no harm) to explicitly list the trait `object` as
an extendee in a class or trait declaration.

Traits `object?` and  `object` contain no members.

The dynamic allocation of objects is done using `new C`...,
 where `C` is the name of a class.
 The name `C` is not allowed to be a trait,
 except that it is allowed to be `object`.
 The construction `new object` allocates a new object (of an unspecified class type).
 The construction can be used to create unique references, where no other properties of those references are needed.
(`new object?` makes no sense; always use `new object` instead because the result of
`new` is always non-null.)

### 5.9.2. Inheritance {#sec-inheritance}

The purpose of traits is to be able to express abstraction: a trait
encapsulates a set of behaviors; classes and traits that extend it
_inherit_ those behaviors, perhaps specializing them.

A trait or class may extend multiple other traits.
The traits syntactically listed in a trait or class's `extends` clause
are called its _direct parents_; the _transitive parents_ of a trait or class
are its direct parents, the transitive parents of its direct parents, and
the `object` trait (if it is not itself `object`).
These are sets of traits, in that it does not matter if
there are repetitions of a given trait in a class or trait's direct or
transitive parents. However, if a trait with type parameters is repeated,
it must have the same actual type parameters in each instance.
Furthermore, a trait may not be in its own set of transitive parents; that is,
the graph of traits connected by the directed _extends_ relationship may not
have any cycles.

A class or trait inherits (as if they are copied) all the instance members
of its transitive parents. However, since names may not be overloaded in
Dafny, different members (that is, members with different type signatures)
within the set of transitive parents and the class or trait itself must have different names.[^overload]
This restriction does mean that traits from different sources that
coincidentally use the same name for different purposes cannot be combined
by being part of the set of transitive parents for some new trait or class.

A declaration of  member `C.M` in a class or trait _overrides_ any other declarations
of the same name (and signature) in a transitive parent. `C.M` is then called an
override; a declaration that
does not override anything is called an _original declaration_.

Static members of a trait may not be redeclared;
thus, if there is a body it must be declared in the trait;
the compiler will require a body, though the verifier will not.

[//]: # Caution - a newline (not a blank line) ends a footnote
[^overload]: It is possible to conceive of a mechanism for disambiguating conflicting names, but this would add complexity to the language that does not appear to be needed, at least as yet.

Where traits within an extension hierarchy do declare instance members with the same
name (and thus the same signature), some rules apply. Recall that, for methods,
every declaration includes a specification; if no specification is given
explicitly, a default specification applies. Instance method declarations in traits,
however, need not have a body, as a body can be declared in an override.

For a given non-static method M,

* A trait or class may not redeclare M if it has a transitive parent that declares M and provides a body.
* A trait may but need not provide a body if all its transitive parents that declare M do not declare a body.
* A trait or class may not have more than one transitive parent that declares M with a body.
* A class that has one or more transitive parents that declare M without a body
and no transitive parent that declares M with a body must itself redeclare M
with a body if it is compiled. (The verifier alone does not require a body.)
* Currently (and under debate), the following restriction applies:
if `M` overrides two (or more) declarations, `P.M` and `Q.M`, then either
`P.M` must override `Q.M` or `Q.M` must override `P.M`.

The last restriction above is the current implementation. It effectively limits
inheritance of a method M to a single "chain" of declarations and does not
permit mixins.

Each of any method declarations explicitly or implicitly
includes a specification. In simple cases, those syntactically separate
specifications will be copies of each other (up to renaming to take account
of differing formal parameter names). However they need not be. The rule is
that the specifications of M in a given class or trait must be _as strong as_
M's specifications in a transitive parent.
Here _as strong as_  means that it
must be permitted to call the subtype's M in the context of the supertype's M.
Stated differently, where P and C are a parent trait and a child class or trait,
respectively, then, under the precondition of `P.M`,

* C.M's `requires` clause must be implied by P.M's `requires` clause
* C.M's `ensures` clause must imply P.M's `ensures` clause
* C.M's `reads` set must be a subset of P.M's `reads` set
* C.M's `modifies` set must be a subset of P.M's `modifies` set
* C.M's `decreases` expression must be smaller than or equal to P.M's `decreases` expression

Non-static const and field declarations are also inherited from parent traits.
These may not be redeclared in extending traits and classes.
However, a trait need not initialize a const field with a value.
The class that extends a trait that declares such a const field without an
initializer can initialize the field in a constructor.
If the declaring trait does give
an initial value in the declaration, the extending class or trait may not either
redeclare the field or give it a value in a constructor.

When names are inherited from multiple traits, they must be different.
If two traits declare a common name (even with the same signature),
they cannot both be extendees of the same class or trait.

### 5.9.3. Example of traits
As an example, the following trait represents movable geometric shapes:
<!-- %check-verify -->
```dafny
trait Shape
{
  function method Width(): real
    reads this
    decreases 1
  method Move(dx: real, dy: real)
    modifies this
  method MoveH(dx: real)
    modifies this
  {
    Move(dx, 0.0);
  }
}
``` <!-- %save Shape.tmp -->
Members `Width` and `Move` are _abstract_ (that is, body-less) and can
be implemented differently by different classes that extend the trait.
The implementation of method `MoveH` is given in the trait and thus
is used by all classes that extend `Shape`.  Here are two classes
that each extend `Shape`:
<!-- %check-verify %use Shape.tmp -->
```dafny
class UnitSquare extends Shape
{
  var x: real, y: real
  function method Width(): real 
    decreases 0
  {  // note the empty reads clause
    1.0
  }
  method Move(dx: real, dy: real)
    modifies this
  {
    x, y := x + dx, y + dy;
  }
}

class LowerRightTriangle extends Shape
{
  var xNW: real, yNW: real, xSE: real, ySE: real
  function method Width(): real
    reads this
    decreases 0
  {
    xSE - xNW
  }
  method Move(dx: real, dy: real)
    modifies this
  {
    xNW, yNW, xSE, ySE := xNW + dx, yNW + dy, xSE + dx, ySE + dy;
  }
}
``` <!-- %save UnitSquare.tmp -->
Note that the classes can declare additional members, that they supply
implementations for the abstract members of the trait,
that they repeat the member signatures, and that they are responsible
for providing their own member specifications that both strengthen the
corresponding specification in the trait and are satisfied by the
provided body.
Finally, here is some code that creates two class instances and uses
them together as shapes:
<!-- %check-verify %use UnitSquare.tmp -->
```dafny
method m() {
  var myShapes: seq<Shape>;
  var A := new UnitSquare;
  myShapes := [A];
  var tri := new LowerRightTriangle;
  // myShapes contains two Shape values, of different classes
  myShapes := myShapes + [tri];
  // move shape 1 to the right by the width of shape 0
  myShapes[1].MoveH(myShapes[0].Width());
}
```

<!--PDF NEWPAGE-->
## 5.10. Array types ([grammar](#g-array-type)) {#sec-array-type}

Dafny supports mutable fixed-length _array types_ of any positive
dimension.  Array types are (heap-based) reference types.

`arrayToken` is a kind of [reserved token](#sec-reserved-words),
such as `array`, `array?`, `array2`, `array2?`, `array3`, and so on (but not `array1`).
The type parameter suffix giving the element type can be omitted if the element type can be inferred, though in that case it is likely that the `arrayToken` itself is also
inferrable and can be omitted.

### 5.10.1. One-dimensional arrays

A one-dimensional array of `n` `T` elements may be initialized by
any expression that returns a value of the desired type.
Commonly, [array allocation expressions](#sec-array-allocation) are used.
Some examples are shown here:
<!-- %check-verify %options --relax-definite-assignment -->
```dafny
type T(0)
method m(n: nat) {
  var a := new T[n];
  var b: array<int> := new int[8];
  var c: array := new T[9];
}
```
The initial values of the array elements are arbitrary values of type
`T`. 
A one-dimensional array value can also be assigned using an ordered list of expressions enclosed in square brackets, as follows:
<!-- %no-check -->
```dafny
a := new T[] [t1, t2, t3, t4];
```
The initialization can also use an expression that returns a function of type `nat -> T`:
<!-- %no-check -->
```dafny
a := new int[5](i => i*i);
```
In fact, the initializer can simply be a function name for the right type of function:
<!-- %no-check -->
```dafny
a := new int[5](Square);
```

The length of an array is retrieved using the immutable `Length`
member.  For example, the array allocated with `a := new T[n];` satisfies:
<!-- %no-check -->
```dafny
a.Length == n
```
Once an array is allocated, its length cannot be changed.

For any integer-based numeric `i` in the range `0 <= i < a.Length`,
the _array selection_ expression `a[i]` retrieves element `i` (that
is, the element preceded by `i` elements in the array).  The
element stored at `i` can be changed to a value `t` using the array
update statement:
<!-- %no-check -->
```dafny
a[i] := t;
```

Caveat: The type of the array created by `new T[n]` is
`array<T>`.  A mistake that is simple to make and that can lead to
befuddlement is to write `array<T>` instead of `T` after `new`.
For example, consider the following:
<!-- %check-resolve Types.17.expect -->
```dafny
type T(0)
method m(n: nat) {
  var a := new array<T>;
  var b := new array<T>[n];
  var c := new array<T>(n);  // resolution error
  var d := new array(n);  // resolution error
}
```
The first statement allocates an array of type `array<T>`, but of
unknown length.  The second allocates an array of type
`array<array<T>>` of length `n`, that is, an array that holds `n`
values of type `array<T>`.  The third statement allocates an
array of type `array<T>` and then attempts to invoke an anonymous
constructor on this array, passing argument `n`.  Since `array` has no
constructors, let alone an anonymous constructor, this statement
gives rise to an error.  If the type-parameter list is omitted for a
type that expects type parameters, Dafny will attempt to fill these
in, so as long as the `array` type parameter can be inferred, it is
okay to leave off the "`<T>`" in the fourth statement above.  However,
as with the third statement, `array` has no anonymous constructor, so
an error message is generated.

### 5.10.2. Converting arrays to sequences {#sec-array-to-seq}

One-dimensional arrays support operations that convert a stretch of
consecutive elements into a sequence.  For any array `a` of type
`array<T>`, integer-based numerics `lo` and `hi` satisfying
`0 <= lo <= hi <= a.Length`, the following operations each yields a
`seq<T>`:

 expression          | description
---------------------|------------------------------------
 `a[lo..hi]`         | subarray conversion to sequence
 `a[lo..]`           | drop
 `a[..hi]`           | take
 `a[..]`             | array conversion to sequence

The expression `a[lo..hi]` takes the first `hi` elements of the array,
then drops the first `lo` elements thereof and returns what remains as
a sequence, with length `hi - lo`.
The other operations are special instances of the first.  If `lo` is
omitted, it defaults to `0` and if `hi` is omitted, it defaults to
`a.Length`.
In the last operation, both `lo` and `hi` have been omitted, thus
`a[..]` returns the sequence consisting of all the array elements of
`a`.

The subarray operations are especially useful in specifications.  For
example, the loop invariant of a binary search algorithm that uses
variables `lo` and `hi` to delimit the subarray where the search `key`
may still be found can be expressed as follows:
<!-- %no-check -->
```dafny
key !in a[..lo] && key !in a[hi..]
```
Another use is to say that a certain range of array elements have not
been changed since the beginning of a method:
<!-- %no-check -->
```dafny
a[lo..hi] == old(a[lo..hi])
```
or since the beginning of a loop:
<!-- %no-check -->
```dafny
ghost var prevElements := a[..];
while // ...
  invariant a[lo..hi] == prevElements[lo..hi]
{
  // ...
}
```
Note that the type of `prevElements` in this example is `seq<T>`, if
`a` has type `array<T>`.

A final example of the subarray operation lies in expressing that an
array's elements are a permutation of the array's elements at the
beginning of a method, as would be done in most sorting algorithms.
Here, the subarray operation is combined with the sequence-to-multiset
conversion:
<!-- %no-check -->
```dafny
multiset(a[..]) == multiset(old(a[..]))
```

### 5.10.3. Multi-dimensional arrays {#sec-multi-dimensional-arrays}

An array of 2 or more dimensions is mostly like a one-dimensional
array, except that `new` takes more length arguments (one for each
dimension), and the array selection expression and the array update
statement take more indices.  For example:
<!-- %no-check -->
```dafny
matrix := new T[m, n];
matrix[i, j], matrix[x, y] := matrix[x, y], matrix[i, j];
```
create a 2-dimensional array whose dimensions have lengths `m` and
`n`, respectively, and then swaps the elements at `i,j` and `x,y`.
The type of `matrix` is `array2<T>`, and similarly for
higher-dimensional arrays (`array3<T>`, `array4<T>`, etc.).  Note,
however, that there is no type `array0<T>`, and what could have been
`array1<T>` is actually named just `array<T>`. (Accordingly, `array0` and `array1` are just
normal identifiers, not type names.)

The `new` operation above requires `m` and `n` to be non-negative
integer-based numerics.  These lengths can be retrieved using the
immutable fields `Length0` and `Length1`.  For example, the following
holds for the array created above:
<!-- %no-check -->
```dafny
matrix.Length0 == m && matrix.Length1 == n
```
Higher-dimensional arrays are similar (`Length0`, `Length1`,
`Length2`, ...).  The array selection expression and array update
statement require that the indices are in bounds.  For example, the
swap statement above is well-formed only if:
<!-- %no-check -->
```dafny
0 <= i < matrix.Length0 && 0 <= j < matrix.Length1 &&
0 <= x < matrix.Length0 && 0 <= y < matrix.Length1
```

In contrast to one-dimensional arrays, there is no operation to
convert stretches of elements from a multi-dimensional array to a
sequence.

There is however syntax to create a multi-dimensional array value
using a function: see [Section 9.16](#sec-array-allocation).


<!--PDF NEWPAGE-->
## 5.11. Iterator types ([grammar](#g-iterator-type)) {#sec-iterator-types}

See [Section 7.5](#sec-iterator-specification) for a description of iterator specifications.

An _iterator_ provides a programming abstraction for writing code that
iteratively returns elements.  These CLU-style iterators are
_co-routines_ in the sense that they keep track of their own program
counter and control can be transferred into and out of the iterator
body.

An iterator is declared as follows:
<!-- %no-check -->
```dafny
iterator Iter<T>(_in-params_) yields (_yield-params_)
  _specification_
{
  _body_
}
```
where `T` is a list of type parameters (as usual, if there are no type
parameters, "`<T>`" is omitted). This declaration gives rise to a
reference type with the same name, `Iter<T>`. In the signature,
in-parameters and yield-parameters are the iterator's analog of a
method's in-parameters and out-parameters. The difference is that the
out-parameters of a method are returned to a caller just once, whereas
the yield-parameters of an iterator are returned each time the iterator
body performs a `yield`. The body consists of statements, like in a
method body, but with the availability also of `yield` statements.

From the perspective of an iterator client, the `iterator` declaration
can be understood as generating a class `Iter<T>` with various
members, a simplified version of which is described next.

The `Iter<T>` class contains an anonymous constructor whose parameters
are the iterator's in-parameters:
<!-- %no-check -->
```dafny
predicate Valid()
constructor (_in-params_)
  modifies this
  ensures Valid()
```
An iterator is created using `new` and this anonymous constructor.
For example, an iterator willing to return ten consecutive integers
from `start` can be declared as follows:
<!-- %check-verify -->
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
``` <-- %save Gen.tmp -->
An instance of this iterator is created using
<!-- %no-check -->
```dafny
iter := new Gen(30);
```
It is used like this:
<!-- %check-verify %use Gen.tmp -->
```dafny
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

The predicate `Valid()` says when the iterator is in a state where one
can attempt to compute more elements.  It is a postcondition of the
constructor and occurs in the specification of the `MoveNext` member:
<!-- %no-check -->
```dafny
method MoveNext() returns (more: bool)
  requires Valid()
  modifies this
  ensures more ==> Valid()
```
Note that the iterator remains valid as long as `MoveNext` returns
`true`.  Once `MoveNext` returns `false`, the `MoveNext` method can no
longer be called.  Note, the client is under no obligation to keep
calling `MoveNext` until it returns `false`, and the body of the
iterator is allowed to keep returning elements forever.

The in-parameters of the iterator are stored in immutable fields of
the iterator class.  To illustrate in terms of the example above, the
iterator class `Gen` contains the following field:
<!-- %no-check -->
```dafny
const start: int
```
The yield-parameters also result in members of the iterator class:
<!-- %no-check -->
```dafny
var x: int
```
These fields are set by the `MoveNext` method.  If `MoveNext` returns
`true`, the latest yield values are available in these fields and the
client can read them from there.

To aid in writing specifications, the iterator class also contains
ghost members that keep the history of values returned by
`MoveNext`.  The names of these ghost fields follow the names of the
yield-parameters with an "`s`" appended to the name (to suggest
plural).  Name checking rules make sure these names do not give rise
to ambiguities.  The iterator class for `Gen` above thus contains:
<!-- %no-check -->
```dafny
ghost var xs: seq<int>
```
These history fields are changed automatically by `MoveNext`, but are
not assignable by user code.

Finally, the iterator class contains some special fields for use in
specifications.  In particular, the iterator specification is
recorded in the following immutable fields:
<!-- %no-check -->
```dafny
ghost var _reads: set<object>
ghost var _modifies: set<object>
ghost var _decreases0: T0
ghost var _decreases1: T1
// ...
```
where there is a `_decreases(`_i_`): T(`_i_`)` field for each
component of the iterator's `decreases`
clause.[^fn-iterator-field-names]
In addition, there is a field:
<!-- %no-check -->
```dafny
ghost var _new: set<object>;
```
to which any objects allocated on behalf of the iterator body are
added.  The iterator body is allowed to remove elements from the
`_new` set, but cannot by assignment to `_new` add any elements.

[^fn-iterator-field-names]:  It would make sense to rename the special
    fields `_reads` and `_modifies` to have the same names as the
    corresponding keywords, `reads` and `modifies`, as is done for
    function values.  Also, the various `_decreases\(_i_\)` fields can be
    combined into one field named `decreases` whose type is a
    _n_-tuple. These changes may be incorporated into a future version
    of Dafny.

Note, in the precondition of the iterator, which is to hold upon
construction of the iterator, the in-parameters are indeed
in-parameters, not fields of `this`.

It is regrettably tricky to use iterators. The language really
ought to have a `foreach` statement to make this easier.
Here is an example showing a definition and use of an iterator.

<!-- %check-verify -->
```dafny
iterator Iter<T(0)>(s: set<T>) yields (x: T)
  yield ensures x in s && x !in xs[..|xs|-1];
  ensures s == set z | z in xs;
{
  var r := s;
  while (r != {})
    invariant r !! set z | z in xs
    invariant s == r + set z | z in xs;
  {
    var y :| y in r;
    assert y !in xs;
    r, x := r - {y}, y;
    assert y !in xs;
    yield;
    assert y == xs[|xs|-1]; // a lemma to help prove loop invariant
  }
}

method UseIterToCopy<T(0)>(s: set<T>) returns (t: set<T>)
  ensures s == t;
{
  t := {};
  var m := new Iter(s);
  while (true)
    invariant m.Valid() && fresh(m._new);
    invariant t == set z | z in m.xs;
    decreases s - t;
  {
    var more := m.MoveNext();
    if (!more) { break; }
    t := t + {m.x};
  }
}
```

The design of iterators is [under discussion and may change](https://github.com/dafny-lang/dafny/issues/2440).

<!--
Make this a heading if it is uncommented
 16. Async-task types

Another experimental feature in Dafny that is likely to undergo some
evolution is _asynchronous methods_.  When an asynchronous method is
called, it does not return values for the out-parameters, but instead
returns an instance of an _async-task type_.  An asynchronous method
declared in a class `C` with the following signature:
<!-- %no-check -->
```dafny
async method AM<T>(\(_in-params_\)) returns (\(_out-params_\))
```
also gives rise to an async-task type `AM<T>` (outside the enclosing
class, the name of the type needs the qualification `C.AM<T>`).  The
async-task type is a reference type and can be understood as a class
with various members, a simplified version of which is described next.

Each in-parameter `x` of type `X` of the asynchronous method gives
rise to a immutable ghost field of the async-task type:
<!-- %no-check -->
```dafny
ghost var x: X;
```
Each out-parameter `y` of type `Y` gives rise to a field
<!-- %no-check -->
```dafny
var y: Y;
```
These fields are changed automatically by the time the asynchronous
method is successfully awaited, but are not assignable by user code.

The async-task type also gets a number of special fields that are used
to keep track of dependencies, outstanding tasks, newly allocated
objects, etc.  These fields will be described in more detail as the
design of asynchronous methods evolves.

-->

<!--PDF NEWPAGE-->
## 5.12. Arrow types ([grammar](#g-arrow-type)) {#sec-arrow-types}

Examples:
<!-- %no-check -->
```dafny
(int) -> int
(bool,int) ~> bool
() --> object?
```

Functions are first-class values in Dafny. The types of function values
are called _arrow types_ (aka, _function types_).
Arrow types have the form `(TT) ~> U` where `TT` is a (possibly empty)
comma-delimited list of types and `U` is a type.
`TT` is called the function's _domain type(s)_ and `U` is its
_range type_.  For example, the type of a function
<!-- %check-resolve -->
```dafny
function F(x: int, arr: array<bool>): real
  requires x < 1000
  reads arr
```
is `(int, array<bool>) ~> real`.

As seen in the example above, the functions that are values of a type
`(TT) ~> U` can have a precondition (as indicated by the `requires` clause)
and can read values in the heap (as indicated by the `reads` clause).
As described in [Section 5.6.3.3](#sec-arrow-subset-types),

- the subset type `(TT) --> U` denotes partial (but heap-independent) functions
- and the subset type `(TT) -> U` denotes total functions.

A function declared without a `reads` clause is known by the type
checker to be a partial function. For example, the type of
<!-- %check-resolve -->
```dafny
function F(x: int, b: bool): real
  requires x < 1000
```
is `(int, bool) --> real`.
Similarly, a function declared with neither a `reads` clause nor a
`requires` clause is known by the type checker to be a total function.
For example, the type of
<!-- %check-resolve -->
```dafny
function F(x: int, b: bool): real
```
is `(int, bool) -> real`.
In addition to functions declared by name, Dafny also supports anonymous
functions by means of _lambda expressions_ (see [Section 9.13](#sec-lambda-expression)).

To simplify the appearance of the basic case where a function's
domain consists of a list of exactly one non-function, non-tuple type, the parentheses around
the domain type can be dropped in this case. For example, you may
write just `T -> U` for a total arrow type.
This innocent simplification requires additional explanation in the
case where that one type is a tuple type, since tuple types are also
written with enclosing parentheses.
If the function takes a single argument that is a tuple, an additional
set of parentheses is needed.  For example, the function
<!-- %check-resolve -->
```dafny
function G(pair: (int, bool)): real
```
has type `((int, bool)) -> real`.  Note the necessary double
parentheses.  Similarly, a function that takes no arguments is
different from one that takes a 0-tuple as an argument.  For instance,
the functions
<!-- %check-resolve -->
```dafny
function NoArgs(): real
function Z(unit: ()): real
```
have types `() -> real` and `(()) -> real`, respectively.

The function arrows are right associative.
For example, `A -> B -> C` means `A -> (B -> C)`, whereas
the other association requires explicit parentheses: `(A -> B) -> C`.
As another example, `A -> B --> C ~> D` means
`A -> (B --> (C ~> D))`.

Note that the receiver parameter of a named function is not part of
the type.  Rather, it is used when looking up the function and can
then be thought of as being captured into the function definition.
For example, suppose function `F` above is declared in a class `C` and
that `c` references an object of type `C`; then, the following is type
correct:
<!-- %no-check -->
```dafny
var f: (int, bool) -> real := c.F;
```
whereas it would have been incorrect to have written something like:
<!-- %no-check -->
```dafny
var f': (C, int, bool) -> real := F;  // not correct
```

The arrow types themselves do not divide a function's parameters into ghost
versus non-ghost. Instead, a function used as a first-class value is
considered to be ghost if either the function or any of its arguments
is ghost. The following example program illustrates:
<!-- %check-resolve Types.18.expect -->
```dafny
function method F(x: int, ghost y: int): int
{
  x
}

method Example() {
  ghost var f: (int, int) -> int;
  var g: (int, int) -> int;
  var h: (int) -> int;
  var x: int;
  f := F;
  x := F(20, 30);
  g := F; // error: tries to assign ghost to non-ghost
  h := F; // error: wrong arity (and also tries to assign ghost to non-ghost)
}
```

In addition to its type signature, each function value has three properties,
described next.

Every function implicitly takes the heap as an argument.  No function
ever depends on the _entire_ heap, however.  A property of the
function is its declared upper bound on the set of heap locations it
depends on for a given input.  This lets the verifier figure out that
certain heap modifications have no effect on the value returned by a
certain function.  For a function `f: T ~> U` and a value `t` of type
`T`, the dependency set is denoted `f.reads(t)` and has type
`set<object>`.

The second property of functions stems from the fact that every function
is potentially _partial_. In other words, a property of a function is its
_precondition_. For a function `f: T ~> U`, the precondition of `f` for a
parameter value `t` of type `T` is denoted `f.requires(t)` and has type
`bool`.

The third property of a function is more obvious---the function's
body.  For a function `f: T ~> U`, the value that the function yields
for an input `t` of type `T` is denoted `f(t)` and has type `U`.

Note that `f.reads` and `f.requires` are themselves functions.
Suppose `f` has type `T ~> U` and `t` has type `T`.  Then, `f.reads`
is a function of type `T ~> set<object?>` whose `reads` and `requires`
properties are:
<!-- %no-check -->
```dafny
f.reads.reads(t) == f.reads(t)
f.reads.requires(t) == true
```
`f.requires` is a function of type `T ~> bool` whose `reads` and
`requires` properties are:
<!-- %no-check -->
```dafny
f.requires.reads(t) == f.reads(t)
f.requires.requires(t) == true
```
In these examples, if `f` instead had type `T --> U` or `T -> U`,
then the type of `f.reads` is `T -> set<object?>` and the type
of `f.requires` is `T -> bool`.

Dafny also supports anonymous functions by means of
_lambda expressions_. See [Section 9.13](#sec-lambda-expression).

<!--PDF NEWPAGE-->
## 5.13.  Tuple types {#sec-tuple-types}
````grammar
TupleType = "(" [ [ "ghost" ] Type { "," [ "ghost" ] Type } ] ")"
````

Dafny builds in record types that correspond to tuples and gives these
a convenient special syntax, namely parentheses.  For example, for what
might have been declared as
<!-- %check-resolve -->
```dafny
datatype Pair<T,U> = Pair(0: T, 1: U)
```
Dafny provides the type `(T, U)` and the constructor `(t, u)`, as
if the datatype's name were "" (i.e., an empty string)
and its type arguments are given in
round parentheses, and as if the constructor name were the empty string.
Note that
the destructor names are `0` and `1`, which are legal identifier names
for members.  For an example showing the use of a tuple destructor, here
is a property that holds of 2-tuples (that is, _pairs_):
<!-- %check-verify -->
```dafny
method m(){
  assert (5, true).1 == true;
}
```

Dafny declares _n_-tuples where _n_ is 0 or 2 or more.  There are no
1-tuples, since parentheses around a single type or a single value have
no semantic meaning.  The 0-tuple type, `()`, is often known as the
_unit type_ and its single value, also written `()`, is known as _unit_.

The `ghost` modifier can be used to mark tuple components as being used for specification only:
<!-- %check-resolve -->
```dafny
const pair: (int, ghost int) := (1, ghost 2)
```

<!--PDF NEWPAGE-->
## 5.14. Algebraic Datatypes ([grammar](#g-datatype)) {#sec-datatype}

Dafny offers two kinds of algebraic datatypes, those defined
inductively (with `datatype`)  and those defined coinductively (with `codatatype`).
The salient property of
every datatype is that each value of the type uniquely identifies one
of the datatype's constructors and each constructor is injective in
its parameters.

### 5.14.1. Inductive datatypes {#sec-inductive-datatypes}

The values of inductive datatypes can be seen as finite trees where
the leaves are values of basic types, numeric types, reference types,
coinductive datatypes, or arrow types.  Indeed, values of
inductive datatypes can be compared using Dafny's well-founded
`<` ordering.

An inductive datatype is declared as follows:
<!-- %no-check -->
```dafny
datatype D<T> = _Ctors_
```
where _Ctors_ is a nonempty `|`-separated list of
_(datatype) constructors_ for the datatype.  Each constructor has the
form:
```text
C(_params_)
```
where _params_ is a comma-delimited list of types, optionally
preceded by a name for the parameter and a colon, and optionally
preceded by the keyword `ghost`.  If a constructor has no parameters,
the parentheses after the constructor name may be omitted.  If no
constructor takes a parameter, the type is usually called an
_enumeration_; for example:
<!-- %check-resolve -->
```dafny
datatype Friends = Agnes | Agatha | Jermaine | Jack
```

For every constructor `C`, Dafny defines a _discriminator_ `C?`, which
is a member that returns `true` if and only if the datatype value has
been constructed using `C`.  For every named parameter `p` of a
constructor `C`, Dafny defines a _destructor_ `p`, which is a member
that returns the `p` parameter from the `C` call used to construct the
datatype value; its use requires that `C?` holds.  For example, for
the standard `List` type
<!-- %check-resolve -->
```dafny
datatype List<T> = Nil | Cons(head: T, tail: List<T>)
``` <!-- %save List.tmp -->
the following holds:
<!-- %check-verify %use List.tmp -->
```dafny
method m() {
  assert Cons(5, Nil).Cons? && Cons(5, Nil).head == 5;
}
```
Note that the expression
<!-- %no-check -->
```dafny
Cons(5, Nil).tail.head
```
is not well-formed, since `Cons(5, Nil).tail` does not necessarily satisfy
`Cons?`.

A constructor can have the same name as
the enclosing datatype; this is especially useful for
single-constructor datatypes, which are often called
_record types_.  For example, a record type for black-and-white pixels
might be represented as follows:
<!-- %check-resolve -->
```dafny
datatype Pixel = Pixel(x: int, y: int, on: bool)
```

To call a constructor, it is usually necessary only to mention the
name of the constructor, but if this is ambiguous, it is always
possible to qualify the name of constructor by the name of the
datatype.  For example, `Cons(5, Nil)` above can be written
<!-- %no-check -->
```dafny
List.Cons(5, List.Nil)
```

As an alternative to calling a datatype constructor explicitly, a
datatype value can be constructed as a change in one parameter from a
given datatype value using the _datatype update_ expression.  For any
`d` whose type is a datatype that includes a constructor `C` that has
a parameter (destructor) named `f` of type `T`, and any expression `t`
of type `T`,
<!-- %no-check -->
```dafny
d.(f := t)
```
constructs a value like `d` but whose `f` parameter is `t`.  The
operation requires that `d` satisfies `C?`.  For example, the
following equality holds:
<!-- %check-verify %use List.tmp -->
```dafny
method m(){
  assert Cons(4, Nil).(tail := Cons(3, Nil)) == Cons(4, Cons(3, Nil));
}
```

The datatype update expression also accepts multiple field
names, provided these are distinct. For example, a node of some
inductive datatype for trees may be updated as follows:

<!-- %no-check -->
```dafny
node.(left := L, right := R)
```

The operator `<` is defined for two operands of the same datataype.
It means _is properly contained in_. For example, in the code
<!-- %check-verify Types.19.expect -->
```dafny
datatype X = T(t: X) | I(i: int)
method comp() {
  var x := T(I(0));
  var y := I(0);
  var z := I(1);
  assert x.t < x;
  assert y < x;
  assert !(x < x);
  assert z < x; // FAILS
}
```
`x` is a datatype value that holds a `T` variant, which holds a `I` variant, which holds an integer `0`.
The value `x.t` is a portion of the datatype structure denoted by `x`, so `x.t < x` is true.
Datatype values are immutable mathematical values, so the value of `y` is identical to the value of
`x.t`, so `y < x` is true also, even though `y` is constructed from the ground up, rather than as
a portion of `x`. However, `z` is different than either `y` or `x.t` and consequently `z < x` is not provable.
Furthermore, `<` does not include `==`, so `x < x` is false.

Note that only `<` is defined; not `<=` or `>` or `>=`.

Also, `<` is underspecified. With the above code, one can prove neither `z < x` nor `!(z < x)` and neither
`z < y` nor `!(z < y)`. In each pair, though, one or the other is true, so `(z < x) || !(z < x)` is provable.

### 5.14.2. Coinductive datatypes {#sec-coinductive-datatypes}

Whereas Dafny insists that there is a way to construct every inductive
datatype value from the ground up, Dafny also supports
_coinductive datatypes_, whose constructors are evaluated lazily, and
hence the language allows infinite structures.
A coinductive datatype is declared
using the keyword `codatatype`; other than that, it is declared and
used like an inductive datatype.

For example,
<!-- %check-verify -->
```dafny
codatatype IList<T> = Nil | Cons(head: T, tail: IList<T>)
codatatype Stream<T> = More(head: T, tail: Stream<T>)
codatatype Tree<T> = Node(left: Tree<T>, value: T, right: Tree<T>)
```
declare possibly infinite lists (that is, lists that can be either
finite or infinite), infinite streams (that is, lists that are always
infinite), and infinite binary trees (that is, trees where every
branch goes on forever), respectively.

The paper [Co-induction Simply](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/coinduction.pdf), by Leino and
Moskal[@LEINO:Dafny:Coinduction], explains Dafny's implementation and
verification of coinductive types. We capture the key features from that
paper in the following section but the reader is referred to that paper for more
complete details and to supply bibliographic references that are
omitted here.

### 5.14.3. Coinduction {#sec-coinduction}

Mathematical induction is a cornerstone of programming and program
verification. It arises in data definitions (e.g., some algebraic data
structures can be described using induction), it underlies program
semantics (e.g., it explains how to reason about finite iteration and
recursion), and it is used in proofs (e.g., supporting lemmas about
data structures use inductive proofs). Whereas induction deals with
finite things (data, behavior, etc.), its dual, coinduction, deals with
possibly infinite things. Coinduction, too, is important in programming
and program verification: it arises in data definitions (e.g., lazy
data structures), semantics (e.g., concurrency), and proofs (e.g.,
showing refinement in a coinductive big-step semantics). It is thus
desirable to have good support for both induction and coinduction in a
system for constructing and reasoning about programs.

Co-datatypes and co-recursive functions make it possible to use lazily
evaluated data structures (like in Haskell or Agda). _Greatest predicates_,
defined by greatest fix-points, let programs state properties of such
data structures (as can also be done in, for example, Coq). For the
purpose of writing coinductive proofs in the language, we introduce
greatest and least lemmas. A greatest lemma invokes the coinduction hypothesis
much like an inductive proof invokes the induction hypothesis. Underneath
the hood, our coinductive proofs are actually approached via induction:
greatest and least lemmas provide a syntactic veneer around this approach.

The following example gives a taste of how the coinductive features in
Dafny come together to give straightforward definitions of infinite
matters.
<!-- %check-verify Types.20.expect -->
```dafny
// infinite streams
codatatype IStream<T> = ICons(head: T, tail: IStream<T>)

// pointwise product of streams
function Mult(a: IStream<int>, b: IStream<int>): IStream<int>
{ ICons(a.head * b.head, Mult(a.tail, b.tail)) }

// lexicographic order on streams
greatest predicate Below(a: IStream<int>, b: IStream<int>)
{ a.head <= b.head &&
  ((a.head == b.head) ==> Below(a.tail, b.tail))
}

// a stream is Below its Square
greatest lemma Theorem_BelowSquare(a: IStream<int>)
  ensures Below(a, Mult(a, a))
{ assert a.head <= Mult(a, a).head;
  if a.head == Mult(a, a).head {
    Theorem_BelowSquare(a.tail);
  }
}

// an incorrect property and a bogus proof attempt
greatest lemma NotATheorem_SquareBelow(a: IStream<int>)
  ensures Below(Mult(a, a), a); // ERROR
{
  NotATheorem_SquareBelow(a);
}
```

The example defines a type `IStream` of infinite streams, with constructor `ICons` and
destructors `head` and `tail`. Function `Mult` performs pointwise
multiplication on infinite streams of integers, defined using a
co-recursive call (which is evaluated lazily). Greatest predicate `Below` is
defined as a greatest fix-point, which intuitively means that the
co-predicate will take on the value true if the recursion goes on forever
without determining a different value. The greatest lemma states the theorem
`Below(a, Mult(a, a))`. Its body gives the proof, where the recursive
invocation of the co-lemma corresponds to an invocation of the
coinduction hypothesis.

The proof of the theorem stated by the first co-lemma lends
itself to the following intuitive reading: To prove that `a` is below
`Mult(a, a)`, check that their heads are ordered and, if the heads are
equal, also prove that the tails are ordered. The second co-lemma states
a property that does not always hold; the verifier is not fooled by the
bogus proof attempt and instead reports the property as unproved.

We argue that these definitions in Dafny are simple enough to level the
playing field between induction (which is familiar) and coinduction
(which, despite being the dual of induction, is often perceived as eerily
mysterious). Moreover, the automation provided by our SMT-based verifier
reduces the tedium in writing coinductive proofs. For example, it
verifies `Theorem_BelowSquare` from the program text given above---no
additional lemmas or tactics are needed. In fact, as a consequence of the
automatic-induction heuristic in Dafny, the verifier will
automatically verify `Theorem_BelowSquare` even given an empty body.

Just like there are restrictions on when an _inductive hypothesis_ can be
invoked, there are restrictions on how a _coinductive_ hypothesis can be
_used_. These are, of course, taken into consideration by Dafny's verifier.
For example, as illustrated by the second greatest lemma above, invoking the
coinductive hypothesis in an attempt to obtain the entire proof goal is
futile. (We explain how this works in [the section about greatest lemmas](#sec-colemmas)) Our initial experience
with coinduction in Dafny shows it to provide an intuitive, low-overhead
user experience that compares favorably to even the best of today’s
interactive proof assistants for coinduction. In addition, the
coinductive features and verification support in Dafny have other
potential benefits. The features are a stepping stone for verifying
functional lazy programs with Dafny. Coinductive features have also
shown to be useful in defining language semantics, as needed to verify
the correctness of a compiler, so this opens the possibility that
such verifications can benefit from SMT automation.

#### 5.14.3.1. Well-Founded Function/Method Definitions
The Dafny programming language supports functions and methods. A _function_
in Dafny is a mathematical function (i.e., it is well-defined,
deterministic, and pure), whereas a _method_ is a body of statements that
can mutate the state of the program. A function is defined by its given
body, which is an expression. To ensure that function definitions
are mathematically consistent, Dafny insists that recursive calls be well-founded,
enforced as follows: Dafny computes the call graph of functions. The strongly connected
components within it are _clusters_ of mutually recursive definitions; the clusters are arranged in
a DAG. This stratifies the functions so that a call from one cluster in the DAG to a
lower cluster is allowed arbitrarily. For an intra-cluster call, Dafny prescribes a proof
obligation that is taken through the program verifier’s reasoning engine. Semantically,
each function activation is labeled by a _rank_—a lexicographic tuple determined
by evaluating the function’s `decreases` clause upon invocation of the function. The
proof obligation for an intra-cluster call is thus that the rank of the callee is strictly less
(in a language-defined well-founded relation) than the rank of the caller. Because
these well-founded checks correspond to proving termination of executable code, we
will often refer to them as “termination checks”. The same process applies to methods.

Lemmas in Dafny are commonly introduced by declaring a method, stating
the property of the lemma in the _postcondition_ (keyword `ensures`) of
the method, perhaps restricting the domain of the lemma by also giving a
_precondition_ (keyword `requires`), and using the lemma by invoking
the method. Lemmas are stated, used, and proved as methods, but
since they have no use at run time, such lemma methods are typically
declared as _ghost_, meaning that they are not compiled into code. The
keyword `lemma` introduces such a method. Control flow statements
correspond to proof techniques—case splits are introduced with if
statements, recursion and loops are used for induction, and method calls
for structuring the proof. Additionally, the statement:
<!-- %no-check -->
```dafny
forall x | P(x) { Lemma(x); }
```
is used to invoke `Lemma(x)` on all `x` for which `P(x)` holds. If
`Lemma(x)` ensures `Q(x)`, then the forall statement establishes
<!-- %no-check -->
```dafny
forall x :: P(x) ==> Q(x).
```

#### 5.14.3.2. Defining Coinductive Datatypes
Each value of an inductive datatype is finite, in the sense that it can
be constructed by a finite number of calls to datatype constructors. In
contrast, values of a coinductive datatype, or co-datatype for short,
can be infinite. For example, a co-datatype can be used to represent
infinite trees.

Syntactically, the declaration of a co-datatype in Dafny looks like that
of a datatype, giving prominence to the constructors (following Coq). The
following example defines a co-datatype Stream of possibly
infinite lists.

<!-- %check-verify -->
```dafny
codatatype Stream<T> = SNil | SCons(head: T, tail: Stream)
function Up(n: int): Stream<int> { SCons(n, Up(n+1)) }
function FivesUp(n: int): Stream<int>
  decreases 4 - (n - 1) % 5
{
  if (n % 5 == 0) then
    SCons(n, FivesUp(n+1))
  else
    FivesUp(n+1)
}
``` <!-- %save Stream.tmp -->

`Stream` is a coinductive datatype whose values are possibly infinite
lists. Function `Up` returns a stream consisting of all integers upwards
of `n` and `FivesUp` returns a stream consisting of all multiples of 5
upwards of `n` . The self-call in `Up` and the first self-call in `FivesUp`
sit in productive positions and are therefore classified as co-recursive
calls, exempt from termination checks. The second self-call in `FivesUp` is
not in a productive position and is therefore subject to termination
checking; in particular, each recursive call must decrease the rank
defined by the `decreases` clause.

Analogous to the common finite list datatype, `Stream` declares two
constructors, `SNil` and `SCons`. Values can be destructed using match
expressions and statements. In addition, like for inductive datatypes,
each constructor `C` automatically gives rise to a discriminator `C?` and
each parameter of a constructor can be named in order to introduce a
corresponding destructor. For example, if `xs` is the stream
`SCons(x, ys)`, then `xs.SCons?` and `xs.head == x` hold. In contrast
to datatype declarations, there is no grounding check for
co-datatypes—since a codatatype admits infinite values, the type is
nevertheless inhabited.

#### 5.14.3.3. Creating Values of Co-datatypes
To define values of co-datatypes, one could imagine a “co-function”
language feature: the body of a “co-function” could include possibly
never-ending self-calls that are interpreted by a greatest fix-point
semantics (akin to a **CoFixpoint** in Coq). Dafny uses a different design:
it offers only functions (not “co-functions”), but it classifies each
intra-cluster call as either _recursive_ or _co-recursive_. Recursive calls
are subject to termination checks. Co-recursive calls may be
never-ending, which is what is needed to define infinite values of a
co-datatype. For example, function `Up(n)` in the preceding example is defined as the
stream of numbers from `n` upward: it returns a stream that starts with `n`
and continues as the co-recursive call `Up(n + 1)`.

To ensure that co-recursive calls give rise to mathematically consistent definitions,
they must occur only in productive positions. This says that it must be possible to determine
each successive piece of a co-datatype value after a finite amount of work. This
condition is satisfied if every co-recursive call is syntactically guarded by a constructor
of a co-datatype, which is the criterion Dafny uses to classify intra-cluster calls as being
either co-recursive or recursive. Calls that are classified as co-recursive are exempt from
termination checks.

A consequence of the productivity checks and termination checks is that, even in the
absence of talking about least or greatest fix-points of self-calling functions, all functions
in Dafny are deterministic. Since there cannot be multiple fix-points,
the language allows one function to be involved in both recursive and co-recursive calls,
as we illustrate by the function `FivesUp`.

#### 5.14.3.5. Co-Equality {#sec-co-equality}
Equality between two values of a co-datatype is a built-in co-predicate.
It has the usual equality syntax `s == t`, and the corresponding prefix
equality is written `s ==#[k] t`. And similarly for `s != t`
and `s !=#[k] t`.

#### 5.14.3.4. Greatest predicates {#sec-copredicates}
Determining properties of co-datatype values may require an infinite
number of observations. To that end, Dafny provides _greatest predicates_
which are function declarations that use the `greatest predicate` keyword phrase.
Self-calls to a greatest predicate need not terminate. Instead, the value
defined is the greatest fix-point of the given recurrence equations.
Continuing the preceding example, the following code defines a
greatest predicate that holds for exactly those streams whose payload consists
solely of positive integers. The greatest predicate definition implicitly also
gives rise to a corresponding prefix predicate, `Pos#`. The syntax for
calling a prefix predicate sets apart the argument that specifies the
prefix length, as shown in the last line; for this figure, we took the
liberty of making up a coordinating syntax for the signature of the
automatically generated prefix predicate (which is not part of
Dafny syntax).

<!-- %check-resolve %use Stream.tmp -->
```dafny
greatest predicate Pos[nat](s: Stream<int>)
{
  match s
  case SNil => true
  case SCons(x, rest) => x > 0 && Pos(rest)
}
``` <!-- %save Pos.tmp -->
The following code is automatically generated by the Dafny compiler:
<!-- %no-check -->
```dafny
predicate Pos#[_k: nat](s: Stream<int>)
  decreases _k
{ if _k == 0 then true else
  match s
  case SNil => true
  case SCons(x, rest) => x > 0 && Pos#[_k-1](rest)
}
```

Some restrictions apply. To guarantee that the greatest fix-point always
exists, the (implicit functor defining the) greatest predicate must be
monotonic. This is enforced by a syntactic restriction on the form of the
body of greatest predicates: after conversion to negation normal form (i.e.,
pushing negations down to the atoms), intra-cluster calls of
greatest predicates must appear only in _positive_ positions—that is, they must
appear as atoms and must not be negated. Additionally, to guarantee
soundness later on, we require that they appear in _continous_
positions—that is, in negation normal form, when they appear under
existential quantification, the quantification needs to be limited to a
finite range[^fn-copredicate-restriction]. Since the evaluation of a greatest predicate might not
terminate, greatest predicates are always ghost. There is also a restriction on
the call graph that a cluster containing a greatest predicate must contain only
greatest predicates, no other kinds of functions.

[^fn-copredicate-restriction]: To be specific, Dafny has two forms of 
extreme predicates and lemmas, one in which `_k` has type `nat` and one in 
which it has type `ORDINAL` (the default). The continuous restriction 
applies only when `_k` is `nat`. Also, higher-order function support in Dafny is
    rather modest and typical reasoning patterns do not involve them, so this
    restriction is not as limiting as it would have been in, e.g., Coq.

A **greatest predicate** declaration of `P` defines not just a greatest predicate, but
also a corresponding _prefix predicate_ `P#`. A prefix predicate is a
finite unrolling of a co-predicate. The prefix predicate is constructed
from the co-predicate by

* adding a parameter `_k` of type `nat` to denote the prefix length,

* adding the clause `decreases _k;` to the prefix predicate (the
  greatest predicate itself is not allowed to have a decreases clause),

* replacing in the body of the greatest predicate every intra-cluster
  call `Q(args)` to a greatest predicate by a call `Q#[_k - 1](args)`
  to the corresponding prefix predicate, and then

* prepending the body with `if _k == 0 then true else`.

For example, for greatest predicate `Pos`, the definition of the prefix
predicate `Pos#` is as suggested above. Syntactically, the prefix-length
argument passed to a prefix predicate to indicate how many times to
unroll the definition is written in square brackets, as in `Pos#[k](s)`.
In the Dafny grammar this is called a ``HashCall``. The definition of
`Pos#` is available only at clusters strictly higher than that of `Pos`;
that is, `Pos` and `Pos#` must not be in the same cluster. In other
words, the definition of `Pos` cannot depend on `Pos#`.

#### 5.14.3.5. Coinductive Proofs
From what we have said so far, a program can make use of properties of
co-datatypes. For example, a method that declares `Pos(s)` as a
precondition can rely on the stream `s` containing only positive integers.
In this section, we consider how such properties are established in the
first place.

##### 5.14.3.5.1. Properties of Prefix Predicates
Among other possible strategies for establishing coinductive properties
we take the time-honored approach of reducing coinduction to
induction. More precisely, Dafny passes to the SMT solver an
assumption `D(P)` for every greatest predicate `P`, where:

<!-- %no-check -->
```dafny
D(P) = forall x • P(x) <==> forall k • P#[k](x)
```

In other words, a greatest predicate is true iff its corresponding prefix
predicate is true for all finite unrollings.

In Sec. 4 of the paper [Co-induction Simply] a soundness theorem of such
assumptions is given, provided the greatest predicates meet the continous
restrictions. An example proof of `Pos(Up(n))` for every `n > 0` is
shown here:

<!-- %check-verify %use Pos.tmp -->
```dafny
lemma UpPosLemma(n: int)
  requires n > 0
  ensures Pos(Up(n))
{
  forall k | 0 <= k { UpPosLemmaK(k, n); }
}

lemma UpPosLemmaK(k: nat, n: int)
  requires n > 0
  ensures Pos#[k](Up(n))
  decreases k
{
  if k != 0 {
    // this establishes Pos#[k-1](Up(n).tail)
    UpPosLemmaK(k-1, n+1);
  }
}
```

The lemma `UpPosLemma` proves `Pos(Up(n))` for every `n > 0`. We first
show `Pos#[k](Up(n ))`, for `n > 0` and an arbitrary `k`, and then use
the forall statement to show `forall k • Pos#[k](Up(n))`. Finally, the axiom
`D(Pos)` is used (automatically) to establish the greatest predicate.


##### 5.14.3.5.2. Greatest lemmas {#sec-colemmas}
As we just showed, with help of the `D` axiom we can now prove a
greatest predicate by inductively proving that the corresponding prefix
predicate holds for all prefix lengths `k`. In this section, we introduce
_greatest lemma_ declarations, which bring about two benefits. The first benefit
is that greatest lemmas are syntactic sugar and reduce the tedium of having to
write explicit quantifications over `k`. The second benefit is that, in
simple cases, the bodies of greatest lemmas can be understood as coinductive
proofs directly. As an example consider the following greatest lemma.

<!-- %no-check -->
```dafny
greatest lemma UpPosLemma(n: int)
  requires n > 0
  ensures Pos(Up(n))
{
  UpPosLemma(n+1);
}
```
This greatest lemma can be understood as follows: `UpPosLemma` invokes itself
co-recursively to obtain the proof for `Pos(Up(n).tail)` (since `Up(n).tail`
equals `Up(n+1)`). The proof glue needed to then conclude `Pos(Up(n))` is
provided automatically, thanks to the power of the SMT-based verifier.

##### 5.14.3.5.3. Prefix Lemmas {#sec-prefix-lemmas}
To understand why the above `UpPosLemma` greatest lemma code is a sound proof,
let us now describe the details of the desugaring of greatest lemmas. In
analogy to how a **greatest predicate** declaration defines both a greatest predicate and
a prefix predicate, a **greatest lemma** declaration defines both a greatest lemma and
_prefix lemma_. In the call graph, the cluster containing a greatest lemma must
contain only greatest lemmas and prefix lemmas, no other methods or function.
By decree, a greatest lemma and its corresponding prefix lemma are always
placed in the same cluster. Both greatest lemmas and prefix lemmas are always
ghost code.

The prefix lemma is constructed from the greatest lemma by

* adding a parameter `_k` of type `nat` to denote the prefix length,

* replacing in the greatest lemma’s postcondition the positive continuous
  occurrences of greatest predicates by corresponding prefix predicates,
  passing in `_k` as the prefix-length argument,

* prepending `_k` to the (typically implicit) **decreases** clause of the greatest lemma,

* replacing in the body of the greatest lemma every intra-cluster call
  `M(args)` to a greatest lemma by a call `M#[_k - 1](args)` to the
  corresponding prefix lemma, and then

* making the body’s execution conditional on `_k != 0`.

Note that this rewriting removes all co-recursive calls of greatest lemmas,
replacing them with recursive calls to prefix lemmas. These recursive
calls are, as usual, checked to be terminating. We allow the pre-declared
identifier `_k` to appear in the original body of the
greatest lemma.[^fn-co-predicate-co-lemma-diffs]

[^fn-co-predicate-co-lemma-diffs]: Note, two places where co-predicates
    and co-lemmas are not analogous are (a) co-predicates must not make
    recursive calls to their prefix predicates and (b) co-predicates cannot
    mention `_k`.

We can now think of the body of the greatest lemma as being replaced by a
**forall** call, for every _k_ , to the prefix lemma. By construction,
this new body will establish the greatest lemma’s declared postcondition (on
account of the `D` axiom, and remembering that only the positive
continuous occurrences of greatest predicates in the greatest lemma’s postcondition
are rewritten), so there is no reason for the program verifier to check
it.

The actual desugaring of our greatest lemma `UpPosLemma` is in fact the
previous code for the `UpPosLemma` lemma except that `UpPosLemmaK` is
named `UpPosLemma#` and modulo a minor syntactic difference in how the
`k` argument is passed.

In the recursive call of the prefix lemma, there is a proof obligation
that the prefixlength argument `_k - 1` is a natural number.
Conveniently, this follows from the fact that the body has been wrapped
in an `if _k != 0` statement. This also means that the postcondition must
hold trivially when `_k == 0`, or else a postcondition violation will be
reported. This is an appropriate design for our desugaring, because
greatest lemmas are expected to be used to establish greatest predicates, whose
corresponding prefix predicates hold trivially when `_k = 0`. (To prove
other predicates, use an ordinary lemma, not a greatest lemma.)

It is interesting to compare the intuitive understanding of the
coinductive proof in using a greatest lemma with the inductive proof in using
a lemma. Whereas the inductive proof is performing proofs for deeper
and deeper equalities, the greatest lemma can be understood as producing the
infinite proof on demand.

# 6. Member declarations

Members are the various kinds of methods, the various kinds of functions, mutable fields,
and constant fields. These are usually associated with classes, but they also may be
declared (with limitations) in traits, newtypes and datatypes (but not in subset types or type synonyms).

## 6.1. Field Declarations ([grammar](#g-field-declaration)) {#sec-field-declaration}

Examples:
<!-- %check-resolve -->
```dafny
class C {
  var c: int  // no initialization
  ghost var 123: bv10  // name may be a sequence of digits
  var d: nat, e: real  // type is required
}
```
A field declaration is not permitted in a value type nor as a member of a module
(despite there being an implicit unnamed class).

The field name is either an
identifier (that is not allowed to start with a leading underscore) or
some digits. Digits are used if you want to number your fields, e.g. "0",
"1", etc. The digits do not denote numbers but sequences of digits,
so 0, 00, 0_0 are all different.

A field x of some type T is declared as:
<!-- %no-check -->
```dafny
var x: T
```

A field declaration declares one or more fields of the enclosing class.
Each field is a named part of the state of an object of that class. A
field declaration is similar to but distinct from a variable declaration
statement. Unlike for local variables and bound variables, the type is
required and will not be inferred.

Unlike method and function declarations, a field declaration
is not permitted as a member of a module, even though there is an implicit class.
Fields can be declared in either an explicit
class or a trait. A class that inherits from multiple traits will
have all the fields declared in any of its parent traits.

Fields that are declared as `ghost` can only be used in specifications,
not in code that will be compiled into executable code.

Fields may not be declared static.

## 6.2. Constant Field Declarations ([grammar](#g-const-declaration)) {#sec-constant-field-declaration}

Examples:
<!-- %check-resolve -->
```dafny
const c: int
ghost const d := 5
class A {
  const e: bool
  static const f: int
}
```
A `const` declaration declares a name bound to a value,
which value is fixed after initialization.

The declaration must either have a type or an initializing expression (or both).
If the type is omitted, it is inferred from the initializing expression.

* A const declaration may include the `ghost`, `static`, and `opaque` modifiers, but no
others.
* A const declaration may appear within a module or within any declaration
that may contain members (class, trait, datatype, newtype).
* If it is in a module, it is implicitly `static`, and may not also be declared
`static`.
* If the declaration has an initializing expression that is a ghost
expression, then the ghost-ness of the declaration is inferred; the `ghost`
modifier may be omitted.
* If the declaration includes the `opaque` modifier, then uses of the declared
variable know its name and type but not its value. The value can be made known for
reasoning purposes by using the [reveal statement](#sec-reveal-statement).
* The initialization expression may refer to other constant fields that are in scope and declared either
before or after this declaration, but circular references are not allowed.

## 6.3. Method Declarations ([grammar](#g-method-declaration)) {#sec-method-declaration}

Examples:
<!-- %check-resolve -->
```dafny
method m(i: int) requires i > 0 {}
method p() returns (r: int) { r := 0; }
method q() returns (r: int, s: int, t: nat) ensures r < s < t { r := 0; s := 1; t := 2; }
ghost method g() {}
class A {
  method f() {}
  constructor Init() {}
  static method g<T>(t: T) {}
}
lemma L(p: bool) ensures p || !p {}
twostate lemma TL(p: bool) ensures p || !p {}
least lemma LL[nat](p: bool) ensures p || !p {}
greatest lemma GL(p: bool) ensures p || !p {}
abstract module M { method m(i: int) }
module N refines M { method m ... {} }
```

Method declarations include a variety of related types of methods:
- method
- constructor
- lemma
- twostate lemma
- least lemma
- greatest lemma

A method signature specifies the method generic parameters,
input parameters and return parameters.
The formal parameters are not allowed to have `ghost` specified
if `ghost` was already specified for the method.
Within the body of a method, formal (input) parameters are immutable, that is, 
they may not be assigned to, though their array elements or fields may be
assigned, if otherwise permitted.
The out-parameters are mutable and must be assigned in the body of the method.

An ``ellipsis`` is used when a method or function is being redeclared
in a module that refines another module. (cf. [Section 10](#sec-module-refinement))
In that case the signature is
copied from the module that is being refined. This works because
Dafny does not support method or function overloading, so the
name of the class method uniquely identifies it without the
signature.

See [Section 7.2](#sec-method-specification) for a description of the method specification.

Here is an example of a method declaration.

<!-- %no-check -->
```dafny
method {:att1}{:att2} M<T1, T2>(a: A, b: B, c: C)
                                        returns (x: X, y: Y, z: Z)
  requires Pre
  modifies Frame
  ensures Post
  decreases Rank
{
  Body
}
```

where `:att1` and `:att2` are attributes of the method,
`T1` and `T2` are type parameters of the method (if generic),
`a, b, c` are the method’s in-parameters, `x, y, z` are the
method’s out-parameters, `Pre` is a boolean expression denoting the
method’s precondition, `Frame` denotes a set of objects whose fields may
be updated by the method, `Post` is a boolean expression denoting the
method’s postcondition, `Rank` is the method’s variant function, and
`Body` is a list of statements that implements the method. `Frame` can be a list
of expressions, each of which is a set of objects or a single object, the
latter standing for the singleton set consisting of that one object. The
method’s frame is the union of these sets, plus the set of objects
allocated by the method body. For example, if `c` and `d` are parameters
of a class type `C`, then

<!-- %no-check -->
```dafny
modifies {c, d}
modifies {c} + {d}
modifies c, {d}
modifies c, d
```

all mean the same thing.

If the method is an _extreme lemma_ ( a `least` or `greatest` lemma), then the 
method signature may also state the type of the _k_ parameter as either `nat` or `ORDINAL`.
These are described
in [Section 12.5.3](#sec-friendliness) and subsequent sections.

### 6.3.1. Ordinary methods

A method can be declared as ghost by preceding the declaration with the
keyword `ghost` and as static by preceding the declaration with the keyword `static`.
The default is non-static (i.e., instance) for methods declared in a type and non-ghost.
An instance method has an implicit receiver parameter, `this`.
A static method M in a class C can be invoked by `C.M(…)`.

An ordinary method is declared with the `method` keyword;
[the section about constructors](#sec-constructor-methods) explains methods that instead use the
`constructor` keyword; [the section about lemmas](#sec-lemmas) discusses methods that are
declared with the `lemma` keyword. Methods declared with the
`least lemma` or `greatest lemma` keyword phrases
are discussed later in the context of extreme
predicates (see [the section about greatest lemmas](#sec-colemmas)).

A method without a body is _abstract_. A method is allowed to be
abstract under the following circumstances:

* It contains an `{:axiom}` attribute
* It contains an `{:extern}` attribute (in this case, to be runnable, the method must have a body in non-Dafny compiled code in the target language.)
* It is a declaration in an abstract module.
Note that when there is no body, Dafny assumes that the *ensures*
clauses are true without proof.

### 6.3.2. Constructors {#sec-constructor-methods}
To write structured object-oriented programs, one often relies on
objects being constructed only in certain ways.  For this purpose, Dafny
provides _constructor (method)s_.
A constructor is declared with the keyword
`constructor` instead of `method`; constructors are permitted only in classes.
A constructor is allowed to be declared as `ghost`, in which case it
can only be used in ghost contexts.

A constructor can only be called at the time an object is allocated (see
object-creation examples below). Moreover, when a class contains a
constructor, every call to `new` for a class must be accompanied
by a call to one of its constructors. A class may
declare no constructors or one or more constructors.

In general, a constructor is responsible for initializating the 
instance fields of its class. However, any field that is given an
initializer in its declaration may not be reassigned in the body
of the constructor.

#### 6.3.2.1. Classes with no explicit constructors

For a class that declares no constructors, an instance of the class is
created with
<!-- %no-check -->
```dafny
c := new C;
```
This allocates an object and initializes its fields to values of their
respective types (and initializes each `const` field with a RHS to its specified
value). The RHS of a `const` field may depend on other `const` or `var` fields,
but circular dependencies are not allowed.

This simple form of `new` is allowed only if the class declares no constructors,
which is not possible to determine in every scope.
It is easy to determine whether or not a class declares any constructors if the
class is declared in the same module that performs the `new`. If the class is
declared in a different module and that module exports a constructor, then it is
also clear that the class has a constructor (and thus this simple form of `new`
cannot be used). (Note that an export set that `reveals` a class `C` also exports
the anonymous constructor of `C`, if any.)
But if the module that declares `C` does not export any constructors
for `C`, then callers outside the module do not know whether or not `C` has a
constructor. Therefore, this simple form of `new` is allowed only for classes that
are declared in the same module as the use of `new`.

The simple `new C` is allowed in ghost contexts. Also, unlike the forms of `new`
that call a constructor or initialization method, it can be used in a simultaneous
assignment; for example
<!-- %no-check -->
```dafny
c, d, e := new C, new C, 15;
```
is legal.

As a shorthand for writing
<!-- %no-check -->
```dafny
c := new C;
c.Init(args);
```
where `Init` is an initialization method (see the top of [the section about class types](#sec-class-types)),
one can write
<!-- %no-check -->
```dafny
c := new C.Init(args);
```
but it is more typical in such a case to declare a constructor for the class.

(The syntactic support for initialization methods is provided for historical
reasons. It may be deprecated in some future version of Dafny. In most cases,
a constructor is to be preferred.)

#### 6.3.2.2. Classes with one or more constructors

Like other class members, constructors have names. And like other members,
their names must be distinct, even if their signatures are different.
Being able to name constructors promotes names like `InitFromList` or
`InitFromSet` (or just `FromList` and `FromSet`).
Unlike other members, one constructor is allowed to be _anonymous_;
in other words, an _anonymous constructor_ is a constructor whose name is
essentially the empty string.  For example:
<!-- %check-resolve -->
```dafny
class Item {
  constructor I(xy: int) // ...
  constructor (x: int, y: int)
  // ...
}
```
The named constructor is invoked as
<!-- %no-check -->
```dafny
  i := new Item.I(42);
```
The anonymous constructor is invoked as
<!-- %no-check -->
```dafny
  m := new Item(45, 29);
```
dropping the "`.`".

#### 6.3.2.3. Two-phase constructors

The body of a constructor contains two sections,
an initialization phase and a post-initialization phase, separated by a `new;` statement.
If there is no `new;` statement, the entire body is the initialization phase.
The initialization phase is intended to initialize field variables
that were not given values in their declaration; it may not reassign
to fields that do have initializers in their declarations.
In this phase, uses of the object reference `this` are restricted;
a program may use `this`

 - as the receiver on the LHS,
 - as the entire RHS of an assignment to a field of `this`,
 - and as a member of a set on the RHS that is being assigned to a field of `this`.

A `const` field with a RHS is not allowed to be assigned anywhere else.
A `const` field without a RHS may be assigned only in constructors, and more precisely
only in the initialization phase of constructors. During this phase, a `const` field
may be assigned more than once; whatever value the `const` field has at the end of the
initialization phase is the value it will have forever thereafter.

For a constructor declared as `ghost`, the initialization phase is allowed to assign
both ghost and non-ghost fields. For such an object, values of non-ghost fields at
the end of the initialization phase are in effect no longer changeable.

There are no restrictions on expressions or statements in the post-initialization phase.

### 6.3.3. Lemmas {#sec-lemmas}
Sometimes there are steps of logic required to prove a program correct,
but they are too complex for Dafny to discover and use on its own. When
this happens, we can often give Dafny assistance by providing a lemma.
This is done by declaring a method with the `lemma` keyword.
Lemmas are implicitly ghost methods and the `ghost` keyword cannot
be applied to them.

Syntactically, lemmas can be placed where ghost methods can be placed, but they serve 
a significantly different function. First of all, a lemma is forbidden to have 
`modifies` clause: it may not change anything about even the ghost state; ghost methods
may have `modifies` clauses and may change ghost (but not non-ghost) state. 
Furthermore, a lemma is not allowed to allocate any new objects.
And a lemma may be used in the program text in places where ghost methods may not,
such as within expressions (cf. [Section 21.1](sec-top-level-expression)).

Lemmas may, but typically do not, have out-parameters.

In summary, a lemma states a logical fact, summarizing an inference that the verifier
cannot do on its own. Explicitly "calling" a lemma in the program text tells the verifier
to use that fact at that location with the actual arguments substituted for the 
formal parameters. The lemma is proved separately for all cases of its formal parameters
that satisfy the preconditions of the lemma. 

For an example, see the `FibProperty` lemma in
[Section 12.5.2](#sec-proofs-in-dafny).

See [the Dafny Lemmas tutorial](../OnlineTutorial/Lemmas)
for more examples and hints for using lemmas.

### 6.3.4. Two-state lemmas and functions {#sec-two-state}

The heap is an implicit parameter to every function, though a function is only allowed
to read those parts of the mutable heap that it admits to in its `reads` clause.
Sometimes, it is useful for a function to take two heap parameters, for example, so
the function can return the difference between the value of a field in the two heaps.
Such a _two-state function_ is declared by `twostate function` (or `twostate predicate`,
which is the same as a `twostate function` that returns a `bool`). A two-state function
is always ghost. It is appropriate to think of these two implicit heap parameters as
representing a "current" heap and an "old" heap.

For example, the predicate
<!-- %check-verify -->
```dafny
class Cell { var data: int  constructor(i: int) { data := i; } }
twostate predicate Increasing(c: Cell)
  reads c
{
  old(c.data) <= c.data
}
``` <!-- %save Increasing.tmp -->
returns `true` if the value of `c.data` has not been reduced from the old state to the
current. Dereferences in the current heap are written as usual (e.g., `c.data`) and
must, as usual, be accounted for in the function's `reads` clause. Dereferences in the
old heap are enclosed by `old` (e.g., `old(c.data)`), just like when one dereferences
a  method's initial heap. The function is allowed to read anything in the old heap;
the `reads` clause only declares dependencies on locations in the current heap.
Consequently, the frame axiom for a two-state function is sensitive to any change
in the old-heap parameter; in other words, the frame axiom says nothing about two
invocations of the two-state function with different old-heap parameters.

At a call site, the two-state function's current-heap parameter is always passed in
as the caller's current heap. The two-state function's old-heap parameter is by
default passed in as the caller's old heap (that is, the initial heap if the caller
is a method and the old heap if the caller is a two-state function). While there is
never a choice in which heap gets passed as the current heap, the caller can use
any preceding heap as the argument to the two-state function's old-heap parameter.
This is done by labeling a state in the caller and passing in the label, just like
this is done with the built-in `old` function.

For example, the following assertions all hold:
<!-- %check-verify %use Increasing.tmp -->
```dafny
method Caller(c: Cell)
  modifies c
{
  c.data := c.data + 10;
  label L:
  assert Increasing(c);
  c.data := c.data - 2;
  assert Increasing(c);
  assert !Increasing@L(c);
}
```
The first call to `Increasing` uses `Caller`'s initial state as the old-heap parameter,
and so does the second call. The third call instead uses as the old-heap parameter
the heap at label `L`, which is why the third call returns `false`.
As shown in the example, an explicitly given old-heap parameter is given after
an `@`-sign (which follows the name of the function and any explicitly given type
parameters) and before the open parenthesis (after which the ordinary parameters are
given).

A two-state function is allowed to be called only from a two-state context, which
means a method, a two-state lemma (see below), or another two-state function.
Just like a label used with an `old` expression, any label used in a call to a
two-state function must denote a program point that _dominates_ the call. This means
that any control leading to the call must necessarily have passed through the labeled
program point.

Any parameter (including the receiver parameter, if any) passed to a two-state function
must have been allocated already in the old state. For example, the second call to
`Diff` in method `M` is illegal, since `d` was not allocated on entry to `M`:
<!-- %check-verify Types.11.expect %use Increasing.tmp -->
```dafny
twostate function Diff(c: Cell, d: Cell): int
  reads d
{
  d.data - old(c.data)
}

method M(c: Cell) {
  var d := new Cell(10);
  label L:
  ghost var x := Diff@L(c, d);
  ghost var y := Diff(c, d); // error: d is not allocated in old state
}
```

A two-state function may declare that it only assumes a parameter to be allocated
in the current heap. This is done by preceding the parameter with the `new` modifier,
as illustrated in the following example, where the first call to `DiffAgain` is legal:
<!-- %check-verify Types.12.expect %use Increasing.tmp -->
```dafny
twostate function DiffAgain(c: Cell, new d: Cell): int
  reads d
{
  d.data - old(c.data)
}

method P(c: Cell) {
  var d := new Cell(10);
  ghost var x := DiffAgain(c, d);
  ghost var y := DiffAgain(d, c); // error: d is not allocated in old state
}
```

A _two-state lemma_ works in an analogous way. It is a lemma with both a current-heap
parameter and an old-heap parameter, it can use `old` expressions in its
specification (including in the precondition) and body, its parameters may
use the `new` modifier, and the old-heap parameter is by default passed in as
the caller's old heap, which can be changed by using an `@`-parameter.

Here is an example of something useful that can be done with a two-state lemma:
<!-- %check-verify %use Increasing.tmp -->
```dafny
function SeqSum(s: seq<Cell>): int
  reads s
{
  if s == [] then 0 else s[0].data + SeqSum(s[1..])
}

twostate lemma IncSumDiff(s: seq<Cell>)
  requires forall c :: c in s ==> Increasing(c)
  ensures old(SeqSum(s)) <= SeqSum(s)
{
  if s == [] {
  } else {
    calc {
      old(SeqSum(s));
    ==  // def. SeqSum
      old(s[0].data + SeqSum(s[1..]));
    ==  // distribute old
      old(s[0].data) + old(SeqSum(s[1..]));
    <=  { assert Increasing(s[0]); }
      s[0].data + old(SeqSum(s[1..]));
    <=  { IncSumDiff(s[1..]); }
      s[0].data + SeqSum(s[1..]);
    ==  // def. SeqSum
      SeqSum(s);
    }
  }
}
```

A two-state function can be used as a first-class function value, where the receiver
(if any), type parameters (if any), and old-heap parameter are determined at the
time the first-class value is mentioned. While the receiver and type parameters can
be explicitly instantiated in such a use (for example, `p.F<int>` for a two-state
instance function `F` that takes one type parameter), there is currently no syntactic
support for giving the old-heap parameter explicitly. A caller can work
around this restriction by using (fancy-word alert!) eta-expansion, meaning
wrapping a lambda expression around the call, as in `x => p.F<int>@L(x)`.
The following example illustrates using such an eta-expansion:
<!-- %check-verify -->
```dafny
class P {
  twostate function F<X>(x: X): X
}

method EtaExample(p: P) returns (ghost f: int -> int) {
  label L:
  f := x => p.F<int>@L(x);
}
```

## 6.4. Function Declarations ([grammar](#g-function-declaration)) {#sec-function-declaration}

### 6.4.1. Functions

Examples:
<!-- %check-resolve -->
```dafny
function f(i: int): real { i as real }
ghost function g(): (int, int) { (2,3) }
function h(i: int, ghost k: int): int requires i >= 0 { if i == 0 then 0 else 1 }
```

Functions may be declared as ghost. If so, all the formal parameters and
return values are ghost; if it is not a ghost function, then 
individual parameters may be declared ghost as desired.

See [Section 7.3](#sec-function-specification) for a description of the function specification.

A Dafny function is a pure mathematical function. It is allowed to
read memory that was specified in its `reads` expression but is not
allowed to have any side effects.

Here is an example function declaration:
<!-- %no-check -->
```dafny
function {:att1}{:att2} F<T1, T2>(a: A, b: B, c: C): T
  requires Pre
  reads Frame
  ensures Post
  decreases Rank
{
  Body
}
```

where `:att1` and `:att2` are attributes of the function, if any, `T1`
and `T2` are type parameters of the function (if generic), `a, b, c` are
the function’s parameters, `T` is the type of the function’s result,
`Pre` is a boolean expression denoting the function’s precondition,
`Frame` denotes a set of objects whose fields the function body may
depend on, `Post` is a boolean expression denoting the function’s
postcondition, `Rank` is the function’s variant function, and `Body` is
an expression that defines the function's return value. The precondition
allows a function to be partial, that is, the precondition says when the
function is defined (and Dafny will verify that every use of the function
meets the precondition).

The postcondition is usually not needed, since
the body of the function gives the full definition. However, the
postcondition can be a convenient place to declare properties of the
function that may require an inductive proof to establish, such as when
the function is recursive. For example:

<!-- %check-verify -->
```dafny
function Factorial(n: int): int
  requires 0 <= n
  ensures 1 <= Factorial(n)
{
  if n == 0 then 1 else Factorial(n-1) * n
}
```

says that the result of Factorial is always positive, which Dafny
verifies inductively from the function body.

Within a postcondition, the result of the function is designated by
a call of the function, such as `Factorial(n)` in the example above.
Alternatively, a name for the function result can be given in the signature,
as in the following rewrite of the example above.

<!-- %check-verify -->
```dafny
function Factorial(n: int): (f: int)
  requires 0 <= n
  ensures 1 <= f
{
  if n == 0 then 1 else Factorial(n-1) * n
}
```

Pre v4.0, a function is `ghost` by default, and cannot be called from non-ghost
code. To make it non-ghost, replace the keyword `function` with the two
keywords "`function method`". From v4.0 on, a function is non-ghost by
default. To make it ghost, replace the keyword `function` with the two keywords "`ghost function`".
(See the [--function-syntax option](#sec-function-syntax) for a description 
of the migration path for this change in behavior.}

Functions (including predicates, function-by-methods, two-state functions, and extreme predicates) may be 
declared `opaque`. In that case, only the signature and specification of the method
is known at its points of use, not its body. The body can be _revealed_ for reasoning
purposes using the [reveal statment](#sec-reveal-statement).

Like methods, functions can be either _instance_ (which they are by default when declared within a type) or
_static_ (when the function declaration contains the keyword `static` or is declared in a module).
An instance function, but not a static function, has an implicit receiver parameter, `this`.  
A static function `F` in a class `C` can be invoked
by `C.F(…)`. This provides a convenient way to declare a number of helper
functions in a separate class.

As for methods, a ``...`` is used when declaring
a function in a module refinement (cf. [Section 10](#sec-module-refinement)).
 For example, if module `M0` declares
function `F`, a module `M1` can be declared to refine `M0` and
`M1` can then refine `F`. The refinement function, `M1.F` can have
a ``...`` which means to copy the signature from
`M0.F`. A refinement function can furnish a body for a function
(if `M0.F` does not provide one). It can also add `ensures`
clauses.

If a function definition does not have a body, the program that contains it may still be verified.
The function itself has nothing to verify.
However, any calls of a body-less function are treated as unverified assumptions by the caller,
asserting the preconditions and assuming the postconditions.
Because body-less functions are unverified assumptions, Dafny will not compile them and will complain if called by [`dafny translate`, `dafny build` or even `dafny run`](#command-line)

### 6.4.2. Predicates
A function that returns a `bool` result is called a _predicate_. As an
alternative syntax, a predicate can be declared by replacing the `function`
keyword with the `predicate` keyword and possibly omitting a declaration of the
return type (if it is not named).

### 6.4.3. Function-by-method {#sec-function-by-method}

A function with a `by method` clause declares a _function-by-method_.
A function-by-method gives a way to implement a
(deterministic, side-effect free) function by a method (whose body may be
nondeterministic and may allocate objects that it modifies). This can
be useful if the best implementation uses nondeterminism (for example,
because it uses `:|` in a nondeterministic way) in a way that does not
affect the result, or if the implementation temporarily makes use of some
mutable data structures, or if the implementation is done with a loop.
For example, here is the standard definition of the Fibonacci function
but with an efficient implementation that uses a loop:

<!-- %check-verify -->
```dafny
function Fib(n: nat): nat {
  if n < 2 then n else Fib(n - 2) + Fib(n - 1)
} by method {
  var x, y := 0, 1;
  for i := 0 to n
    invariant x == Fib(i) && y == Fib(i + 1)
  {
    x, y := y, x + y;
  }
  return x;
}
```

The `by method` clause is allowed only for non-ghost `function` or `predicate`
declarations (without `twostate`, `least`, and `greatest`, but
possibly with `static`); it inherits the in-parameters, attributes, and `requires` and `decreases`
clauses of the function. The method also gets one out-parameter, corresponding
to the function's result value (and the name of it, if present). Finally,
the method gets an empty `modifies` clause and a postcondition
`ensures r == F(args)`, where `r` is the name of the out-parameter and
`F(args)` is the function with its arguments. In other words, the method
body must compute and return exactly what the function says, and must
do so without modifying any previously existing heap state.

The function body of a function-by-method is allowed to be ghost, but the
method body must be compilable. In non-ghost contexts, the compiler turns a
call of the function-by-method into a call that leads to the method body.

Note, the method body of a function-by-method may contain `print` statements.
This means that the run-time evaluation of an expression may have print effects.
If `--track-print-effects` is enabled, this use of print in a function context
will be disallowed.

### 6.4.4. Function Transparency
A function is said to be _transparent_ in a location if the
body of the function is visible at that point.
A function is said to be _opaque_ at a location if it is not
transparent. However the specification of a function
is always available.

A function is usually transparent up to some unrolling level (up to
1, or maybe 2 or 3). If its arguments are all literals it is
transparent all the way.

But the transparency of a function is affected by
whether the function was declared with an `opaque` modifier, as explained
in [Section 11.2.8](#sec-opaque)),
the reveal statement ([Section 8.20](#sec-reveal-statement)),
and whether it was `reveal`ed in an export set.

- Inside the module where the function is declared:
   - if there is no `opaque` modifier, the function is transparent
   - if there is an `opaque` modifier, then the function is opaque,
   except if the function is mentioned in a `reveal` statement, then
   it is transparent between that `reveal` statement and the end of
   the block containing the `reveal` statement.
- Outside the module where the function is declared, the function is 
visible only if it was listed in the export set by which the contents
of its module was imported. In that case, if the function was exported
with `reveals`, the rules are the same within the importing module as when the function is used inside
its declaring module. If the function is exported only with `provides` it is
always opaque and is not permitted to be used in a reveal statement.

### 6.4.5. Extreme (Least or Greatest) Predicates and Lemmas
See [Section 12.5.3](#sec-friendliness) for descriptions
of extreme predicates and lemmas.

### 6.4.6. `older` parameters in predicates {#sec-older-parameters}

A parameter of any predicate (more precisely, of any
boolean-returning, non-extreme function) can be marked as
`older`. This specifies that the truth of the predicate implies that
the allocatedness of the parameter follows from the allocatedness of
the non-`older` parameters.

To understand what this means and why this attribute is useful,
consider the following example, which specifies reachability between
nodes in a directed graph. A `Node` is declared to have any number of
children:

<!-- %check-verify -->
```dafny
class Node {
  var children: seq<Node>
}
``` <!-- %save Node.tmp -->

There are several ways one could specify reachability between
nodes. One way (which is used in `Test/dafny1/SchorrWaite.dfy` in the
Dafny test suite) is to define a type `Path`, representing lists of
`Node`s, and to define a predicate that checks if a given list of
`Node`s is indeed a path between two given nodes:

<!-- %check-verify %use Node.tmp -->
```dafny
datatype Path = Empty | Extend(Path, Node)

predicate ReachableVia(source: Node, p: Path, sink: Node, S: set<Node>)
  reads S
  decreases p
{
  match p
  case Empty =>
    source == sink
  case Extend(prefix, n) =>
    n in S && sink in n.children && ReachableVia(source, prefix, n, S)
}
``` <!-- %save ReachableVia.tmp -->

In a nutshell, the definition of `ReachableVia` says

* An empty path lets `source` reach `sink` just when
  `source` and `sink` are the same node.
* A path `Extend(prefix, n)` lets `source` reach `sink` just when
  the path `prefix` lets `source` reach `n` and `sink` is one of
  the children nodes of `n`.

To be admissible by Dafny, the recursive predicate must be shown to
terminate. Termination is assured by the specification `decreases p`,
since every such datatype value has a finite structure and every
recursive call passes in a path that is structurally included in the
previous. Predicate `ReachableVia` must also declare (an upper bound
on) which heap objects it depends on. For this purpose, the
predicate takes an additional parameter `S`, which is used to limit
the set of intermediate nodes in the path. More precisely, predicate
`ReachableVia(source, p, sink, S)` returns `true` if and only if `p`
is a list of nodes in `S` and `source` can reach `sink` via `p`.

Using predicate `ReachableVia`, we can now define reachability in `S`:

<!-- %check-resolve Types.13.expect %use ReachableVia.tmp -->
```dafny
predicate Reachable(source: Node, sink: Node, S: set<Node>)
  reads S
{
  exists p :: ReachableVia(source, p, sink, S)
}
```

This looks like a good definition of reachability, but Dafny won't
admit it. The reason is twofold:

* Quantifiers and comprehensions are allowed to range only over
  allocated state. Ater all, Dafny is a type-safe language where every
  object reference is _valid_ (that is, a pointer to allocated storage
  of the right type)---it should not be possible, not even through a
  bound variable in a quantifier or comprehension, for a program to
  obtain an object reference that isn't valid.

* This property is ensured by disallowing _open-ended_ quantifiers.
  More precisely, the object references that a quantifier may range
  over must be shown to be confined to object references that were
  allocated before some of the non-`older` parameters passed to the
  predicate. Quantifiers that are not open-ended are called
  _close-ended_. Note that close-ended refers only to the object
  references that the quantification or comprehension ranges over---it
  does not say anything about values of other types, like integers.

Often, it is easy to show that a quantifier is close-ended. In fact,
if the type of a bound variable does not contain any object
references, then the quantifier is trivially close-ended. For example,

<!-- %no-check -->
```dafny
forall x: int :: x <= Square(x)
```

is trivially close-ended.

Another innocent-looking quantifier occurs in the following example:

<!-- %check-resolve Types.14.expect -->
```dafny
predicate IsCommutative<X>(r: (X, X) -> bool)
{
  forall x, y :: r(x, y) == r(y, x) // error: open-ended quantifier
}
```

Since nothing is known about type `X`, this quantifier might be
open-ended.  For example, if `X` were passed in as a class type, then
the quantifier would be open-ended. One way to fix this predicate is
to restrict it to non-heap based types, which is indicated with the
`(!new)` type characteristic (see [Section 5.3.1.4](#sec-non-heap-based)):

<!-- %check-verify -->
```dafny
predicate IsCommutative<X(!new)>(r: (X, X) -> bool) // X is restricted to non-heap types
{
  forall x, y :: r(x, y) == r(y, x) // allowed
}
```

Another way to make `IsCommutative` close-ended is to constrain the values
of the bound variables `x` and `y`. This can be done by adding a parameter
to the predicate and limiting the quantified values to ones in the given set:

<!-- %check-verify -->
```dafny
predicate IsCommutativeInS<X>(r: (X, X) -> bool, S: set<X>)
{
  forall x, y :: x in S && y in S ==> r(x, y) == r(y, x) // close-ended
}
```

Through a simple syntactic analysis, Dafny detects the antecedents
`x in S` and `y in S`, and since `S` is a parameter and thus can only be
passed in as something that the caller has already allocated, the
quantifier in `IsCommutativeInS` is determined to be close-ended.

Note, the `x in S` trick does not work for the motivating example,
`Reachable`. If you try to write

<!-- %check-resolve Types.15.expect %use ReachableVia.tmp -->
```dafny
predicate Reachable(source: Node, sink: Node, S: set<Node>)
  reads S
{
  exists p :: p in S && ReachableVia(source, p, sink, S) // type error: p
}
```

you will get a type error, because `p in S` does not make sense if `p`
has type `Path`. We need some other way to justify that the
quantification in `Reachable` is close-ended.

Dafny offers a way to extend the `x in S` trick to more situations.
This is where the `older` modifier comes in. Before we apply `older`
in the `Reachable` example, let's first look at what `older` does in a
less cluttered example.

Suppose we rewrite `IsCommutativeInS` using a programmer-defined predicate `In`:

<!-- %check-resolve Types.16.expect -->
```dafny
predicate In<X>(x: X, S: set<X>) {
  x in S
}

predicate IsCommutativeInS<X>(r: (X, X) -> bool, S: set<X>)
{
  forall x, y :: In(x, S) && In(y, S) ==> r(x, y) == r(y, x) // error: open-ended?
}
```

The simple syntactic analysis that looks for `x in S` finds nothing
here, because the `in` operator is relegated to the body of predicate
`In`. To inform the analysis that `In` is a predicate that, in effect,
is like `in`, you can mark parameter `x` with `older`:

<!-- %check-verify -->
```dafny
predicate In<X>(older x: X, S: set<X>) {
  x in S
}
```

This causes the simple syntactic analysis to accept the quantifier in
`IsCommutativeInS`. Adding `older` also imposes a semantic check on
the body of predicate `In`, enforced by the verifier. The semantic
check is that all the object references in the value `x` are older (or
equally old as) the object references that are part of the other
parameters, _in the event that the predicate returns true_. That is,
`older` is designed to help the caller only if the predicate returns
`true`, and the semantic check amounts to nothing if the predicate
returns `false`.

Finally, let's get back to the motivating example. To allow the quantifier
in `Reachable`, mark parameter `p` of `ReachableVia` with `older`:

<!-- %check-verify -->
```dafny
class Node {
  var children: seq<Node>
}

datatype Path = Empty | Extend(Path, Node)

predicate Reachable(source: Node, sink: Node, S: set<Node>)
  reads S
{
  exists p :: ReachableVia(source, p, sink, S) // allowed because of 'older p' on ReachableVia
}

predicate ReachableVia(source: Node, older p: Path, sink: Node, S: set<Node>)
  reads S
  decreases p
{
  match p
  case Empty =>
    source == sink
  case Extend(prefix, n) =>
    n in S && sink in n.children && ReachableVia(source, prefix, n, S)
}
```

This example is more involved than the simpler `In` example
above. Because of the `older` modifier on the parameter, the quantifier in
`Reachable` is allowed. For intuition, you can think of the effect of
`older p` as adding an antecedent `p in {source} + {sink} + S`
(but, as we have seen, this is not type correct). The semantic check
imposed on the body of `ReachableVia` makes sure that, if the
predicate returns `true`, then every object reference in `p` is as old
as some object reference in another parameter to the predicate.


