# Types
````grammar
Type = DomainType [ "->" Type ]
````
A Dafny type is a domain type (i.e. a type that can be the domain of a
function type) optionally followed by an arrow and a range type.

````grammar
DomainType =
  ( BoolType_ | CharType_ | IntType_ | RealType_ 
  | OrdinalType_ | BitVectorType_ | ObjectType_
  | FiniteSetType_ | InfiniteSetType_ | MultisetType_
  | SequenceType_ | StringType_
  | FiniteMapType_ | InfiniteMapType_ | ArrayType_
  | TupleType_ | NamedType_ 
  )
````
The domain types comprise the builtin scalar types, the builtin
collection types, tuple types (including as a special case
a parenthesized type) and reference types.

Dafny types may be categorized as either value types or reference types.

## Value Types
The value types are those whose values do not lie in the program heap.
These are:

* The basic scalar types: `bool`, `char`, `int`, `real`, `ORDINAL`, bitvector types
* The built-in collection types: `set`, `multiset`, `seq`, `string`, `map`, `imap`
* Tuple Types
* Inductive and co-inductive types

Data items having value types are passed by value. Since they are not
considered to occupy _memory_, framing expressions do not reference them.

The `nat` type is a pre-defined [subset type](#sec-subset-types) of `int`.

## Reference Types
Dafny offers a host of _reference types_.  These represent
_references_ to objects allocated dynamically in the program heap.  To
access the members of an object, a reference to (that is, a _pointer_
to or _object identity_ of) the object is _dereferenced_.

The reference types are class types, traits and array types.
Dafny supports both reference types that contain the special `null` value 
(_nullable types_) and reference types that do not (_non-null types_).

## Named Types
````grammar
NamedType_ = NameSegmentForTypeName { "." NameSegmentForTypeName }
````

A ``NamedType_`` is used to specify a user-defined type by name
(possibly module-qualified). Named types are introduced by
class, trait, inductive, co-inductive, synonym and opaque
type declarations. They are also used to refer to type variables.

````grammar
NameSegmentForTypeName = Ident  [ GenericInstantiation ]
````
A ``NameSegmentForTypeName`` is a type name optionally followed by a
``GenericInstantiation``, which supplies type parameters to a generic
type, if needed. It is a special case of a ``NameSegment``
(See Section [#sec-name-segment])
that does not allow a ``HashCall``.

The following sections describe each of these kinds of types in more detail.

# Basic types

Dafny offers these basic types: `bool` for booleans, `char` for
characters, `int` and `nat` for integers, `real` for reals,
`ORDINAL`, and bit-vector types..

## Booleans
````grammar
BoolType_ = "bool"
````

There are two boolean values and each has a corresponding literal in
the language:  `false` and `true`.

Type `bool` supports the following operations:

 operator           | description                        
--------------------|------------------------------------
 `<==>`             | equivalence (if and only if)       
--------------------|------------------------------------
 `==>`              | implication (implies)              
 `<==`              | reverse implication (follows from) 
--------------------|------------------------------------
 `&&`               | conjunction (and)                  
 `||`               | disjunction (or)                   
--------------------|------------------------------------
 `==`               | equality                           
 `!=`               | disequality                        
--------------------|------------------------------------
 `!`                | negation (not)                     

Negation is unary; the others are binary.  The table shows the operators
in groups of increasing binding power, with equality binding stronger
than conjunction and disjunction, and weaker than negation.  Within
each group, different operators do not associate, so parentheses need
to be used.  For example,
```dafny
A && B || C    // error
```
would be ambiguous and instead has to be written as either
```dafny
(A && B) || C
```
or
```dafny
A && (B || C)
```
depending on the intended meaning.

### Equivalence Operator
The expressions `A <==> B` and `A == B` give the same value, but note
that `<==>` is _associative_ whereas `==` is _chaining_.  So,
```dafny
A <==> B <==> C
```
is the same as
```dafny
A <==> (B <==> C)
```
and
```dafny
(A <==> B) <==> C
```
whereas
```dafny
A == B == C
```
is simply a shorthand for
```dafny
A == B && B == C
```

### Conjunction and Disjunction
Conjunction and disjunction are associative.  These operators are
_short circuiting (from left to right)_, meaning that their second
argument is evaluated only if the evaluation of the first operand does
not determine the value of the expression.  Logically speaking, the
expression `A && B` is defined when `A` is defined and either `A`
evaluates to `false` or `B` is defined.  When `A && B` is defined, its
meaning is the same as the ordinary, symmetric mathematical
conjunction `&`.  The same holds for `||` and `|`.

### Implication and  Reverse Implication
Implication is _right associative_ and is short-circuiting from left
to right.  Reverse implication `B <== A` is exactly the same as
`A ==> B`, but gives the ability to write the operands in the opposite
order.  Consequently, reverse implication is _left associative_ and is
short-circuiting from _right to left_.  To illustrate the
associativity rules, each of the following four lines expresses the
same property, for any `A`, `B`, and `C` of type `bool`:
```dafny
A ==> B ==> C
A ==> (B ==> C) // parentheses redundant, ==> is right associative
C <== B <== A
(C <== B) <== A // parentheses redundant, <== is left associative
```
To illustrate the short-circuiting rules, note that the expression
`a.Length` is defined for an array `a` only if `a` is not `null` (see
Section [Reference Types](#sec-reference-types)), which means the following two
expressions are well-formed:
```dafny
a != null ==> 0 <= a.Length
0 <= a.Length <== a != null
```
The contrapositives of these two expressions would be:
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
```dafny
a == null || 0 <= a.Length
```
is well-formed, whereas
```dafny
0 <= a.Length || a == null  // not well-formed
```
is not.

In addition, booleans support _logical quantifiers_ (forall and
exists), described in section [Quantifier Expressions](#sec-quantifier-expression).


## Numeric types

````grammar
IntType_ = "int"
RealType_ = "real"
````

Dafny supports _numeric types_ of two kinds, _integer-based_, which
includes the basic type `int` of all integers, and _real-based_, which
includes the basic type `real` of all real numbers.  User-defined
numeric types based on `int` and `real`, either _subset types_ or _newtypes_, are
described in Sections [#sec-subset-types] and  [#sec-newtypes].  
There is one builtin _subset type_,
`nat`, representing the non-negative subrange of `int`.

The language includes a literal for each non-negative integer, like
`0`, `13`, and `1985`.  Integers can also be written in hexadecimal
using the prefix "`0x`", as in `0x0`, `0xD`, and `0x7c1` (always with
a lower case `x`, but the hexadecimal digits themselves are case
insensitive).  Leading zeros are allowed.  To form negative integers,
use the unary minus operator.

There are also literals for some of the non-negative reals.  These are
written as a decimal point with a nonempty sequence of decimal digits
on both sides.  For example, `1.0`, `1609.344`, and `0.5772156649`.

For integers (in both decimal and hexadecimal form) and reals,
any two digits in a literal may be separated by an underscore in order
to improve human readability of the literals.  For example:
```dafny
1_000_000        // easier to read than 1000000
0_12_345_6789    // strange but legal formatting of 123456789
0x8000_0000      // same as 0x80000000 -- hex digits are 
                 // often placed in groups of 4
0.000_000_000_1  // same as 0.0000000001 -- 1 Angstrom
```

In addition to equality and disequality, numeric types
support the following relational operations:

 operator          | description                       
-------------------|------------------------------------
  `<`              | less than                          
  `<=`             | at most                            
  `>=`             | at least                          
  `>`              | greater than                       

Like equality and disequality, these operators are chaining, as long
as they are chained in the "same direction".  That is,
```dafny
A <= B < C == D <= E
```
is simply a shorthand for
```dafny
A <= B && B < C && C == D && D <= E
```
whereas
```dafny
A < B > C
```
is not allowed.

There are also operators on each numeric type:

 operator        | description                        
-----------------|------------------------------------
  `+`            | addition (plus)                    
  `-`            | subtraction (minus)                
-----------------|------------------------------------
  `*`            | multiplication (times)             
  `/`            | division (divided by)              
  `%`            | modulus (mod)  -- int only                     
  -----------------|------------------------------------
`-`            | negation (unary minus)             

The binary operators are left associative, and they associate with
each other in the two groups.  The groups are listed in order of
increasing binding power, with equality binding less strongly than any of these operators.
Modulus is supported only for integer-based numeric types.  Integer
division and modulus are the _Euclidean division and modulus_.  This
means that modulus always returns a non-negative value, regardless of the
signs of the two operands.  More precisely, for any integer `a` and
non-zero integer `b`,
```dafny
a == a / b * b + a % b
0 <= a % b < B
```
where `B` denotes the absolute value of `b`.

Real-based numeric types have a member `Floor` that returns the
_floor_ of the real value (as an int value), that is, the largest integer not exceeding
the real value.  For example, the following properties hold, for any
`r` and `r'` of type `real`:
```dafny
3.14.Floor == 3
(-2.5).Floor == -3
-2.5.Floor == -2
r.Floor as real <= r
r <= r' ==> r.Floor <= r'.Floor
```
Note in the third line that member access (like `.Floor`) binds
stronger than unary minus.  The fourth line uses the conversion
function `real` from `int` to `real`, as described in Section
[#sec-numeric-conversion-operations].

## Bit-vector types
````grammar
BitVectorType_ = "bv" posdigit {digit}
````

Dafny includes a family of bit-vector types, each type having a specific,
constant length, the number of bits in its values. Each such type is
distinct as is designated by the prefix `bv` followed (without white space) by
a positive intiger (without leading zeros) stating the number of bits. For example,
`bv1`, `bv8`, and `bv32` are legal bit-vector type names.

Constant literals of bit-vector types are given by integer literals converted automatically
to the designated type, either by an implic it or explicit conversion operation or by initialization of a declaration.
Dafny checks that the constant literal is in the correct range. For example,
```dafny
{% include Example-BV.dfy %}
```

Bit-vector values can be converted to and from `int` and other bit-vector types, as long as
the values are in range for the target type. Bit-vector values are always considered unsigned.

Bit-vector operations include bit-wise operators and arithmetic operators. The latter
truncate the high-order bits from the results; that is, they perform arithmetic modulo 2<sup>number of bits</sup>, like 2's-complement machine arithmetic.

 operator        | description                        
 -----------------|------------------------------------
 `<<`            | bit-limited bit-shift left                  
  `>>`            | unsigned bit-shift right                 
-----------------|------------------------------------
     `+`            | bit-limited addition                   
    `-`            | bit-limited subtraction                
  -----------------|------------------------------------
  `*`            | bit-limited multiplication             
  -----------------|------------------------------------
 `&`            | bit-wise and                  
  `|`            | bit-wise or                
  `^`            | bit-wise exclusive-or                
-----------------|------------------------------------
`-`            | bit-limited negation (unary minus)             
`!`            | bit-wise complement             

The groups of operators lower in the table above bind more tightly.[^binding] All operators bind more tightly than equality and disequality. All binary operators are left-associative, but the bit-wise `&`, `|`, and `^` do not associate together (parentheses are required to disambiguate). Here are examples of the various operations (all the assertions are truei excepts where indicated):
```dafny
{% include Example-BV2.dfy %}
```
The following are incorrectly formed:
```dafny
{% include Example-BV3.dfy %}
```
These produce assertion errors:
```dafny
{% include Example-BV4.dfy %}
```


TO BE CHECKED: RHS of shift is int type?


[^binding]: The binding power of shift and bit-wise operations is different than in C-like languages.


TO BE WRITTEN  -- are types first class?

## Ordinal type
````grammar
OrdinalType_ = "ORDINAL"
````

TO BE WRITTEN

## Characters

````grammar
CharType_ = "char"
````

Dafny supports a type `char` of _characters_.  Character literals are
enclosed in single quotes, as in `'D'`. Their form is described
by the ``charToken`` nonterminal in the grammar.  To write a single quote as a
character literal, it is necessary to use an _escape sequence_.
Escape sequences can also be used to write other characters.  The
supported escape sequences are the following:

 escape sequence    | meaning                                              
--------------------|-------------------------------------------------------
 `\'`               | the character `'`                                      
 `\"`               | the character `"`                        
 `\\`               | the character `\`                                    
 `\0`               | the null character, same as `\u0000`                
 `\n`               | line feed                                             
 `\r`               | carriage return                                      
 `\t`               | horizontal tab                                      
 `\u`_xxxx_         | universal character whose hexadecimal code is _xxxx_,  where each _x_ is a hexadecimal digit

The escape sequence for a double quote is redundant, because
`'"'` and `'\"'` denote the same
character---both forms are provided in order to support the same
escape sequences in string literals (Section [#sec-strings]).
In the form `\u`_xxxx_, the `u` is always lower case, but the four
hexadecimal digits are case insensitive.

Character values are ordered and can be compared using the standard
relational operators:

 operator        | description                        
-----------------|-----------------------------------
  `<`              | less than                        
  `<=`             | at most                         
  `>=`             | at least                       
  `>`              | greater than                  

Sequences of characters represent _strings_, as described in Section
[#sec-strings].

The only other operations on characters are obtaining a character
by indexing into a string, and the implicit conversion to string
when used as a parameter of a `print` statement.

TODO: Are there any conversions between `char` values and numeric values?

# Type parameters

````grammar
GenericParameters = "<" TypeVariableName [ "(" "==" ")" ]
      { "," TypeVariableName [ "(" "==" ")" ] } ">"
````
Many of the types (as well as functions and methods) in Dafny can be
parameterized by types.  These _type parameters_ are typically
declared inside angle brackets and can stand for any type.

It is sometimes necessary to restrict these type parameters so that
they can only be instantiated by certain families of types.  As such,
Dafny distinguishes types that support the equality operation
in compiled contexts.  To indicate
that a type parameter is restricted to such _equality supporting_
types, the name of the type parameter takes the suffix
"`(==)`".[^fn-type-mode]  For example,
```dafny
method Compare<T(==)>(a: T, b: T) returns (eq: bool)
{
  if a == b { eq := true; } else { eq := false; }
}
```
is a method whose type parameter is restricted to equality-supporting
types.  Again, note that _all_ types support equality in _ghost_
contexts; the difference is only for non-ghost (that is, compiled)
code.  Co-inductive datatypes, function types, as well as inductive
datatypes with ghost parameters are examples of types that are not
equality supporting.

TO BE WRITTEN: There are now more such modes

[^fn-type-mode]:  Being equality-supporting is just one of many
    _modes_ that one can imagine types in a rich type system to have.
    For example, other modes could include having a total order,
    being zero-initializable, and possibly being uninhabited.  If
    Dafny were to support more modes in the future, the "`(\(&nbsp;\))`"-suffix
    syntax may be extended.  For now, the suffix can only indicate the
    equality-supporting mode.

Dafny has some inference support that makes certain signatures less
cluttered (described in a different part of the Dafny language
reference).  In some cases, this support will
infer that a type parameter must be restricted to equality-supporting
types, in which case Dafny adds the "`(==)`" automatically.

TO BE WRITTEN: Type parameter variance with + - = * ! default

TO BE WRITTEN: Type parameter characteristics: == 0 !new

TODO: Need to describe type inference somewhere.

# Generic Instantiation
````grammar
GenericInstantiation = "<" Type { "," Type } ">"
````
When a generic entity is used, actual types must be specified for each
generic parameter. This is done using a ``GenericInstantiation``.
If the `GenericInstantiation` is omitted, type inference will try
to fill these in.

# Collection types

Dafny offers several built-in collection types.

## Sets
````grammar
FiniteSetType_ = "set" [ GenericInstantiation ]
InfiniteSetType_ = "iset" [ GenericInstantiation ]
````

For any type `T`, each value of type `set<T>` is a finite set of
`T` values.

TODO:
Set membership is determined by equality in the type `T`,
so `set<T>` can be used in a non-ghost context only if `T` is equality
supporting.

For any type `T`, each value of type `iset<T>` is a potentially infinite
set of `T` values.

A set can be formed using a _set display_ expression, which is a
possibly empty, unordered, duplicate-insensitive list of expressions
enclosed in curly braces.  To illustrate,
```dafny
{}        {2, 7, 5, 3}        {4+2, 1+5, a*b}
```
are three examples of set displays. There is also a _set comprehension_
expression (with a binder, like in logical quantifications), described in
section [#sec-set-comprehension-expressions].

In addition to equality and disequality, set types
support the following relational operations:

 operator        | description                        
-----------------|------------------------------------
 `<`             | proper subset                      
 `<=`            | subset                             
 `>=`            | superset                           
 `>`             | proper superset                    

Like the arithmetic relational operators, these operators are
chaining.

Sets support the following binary operators, listed in order of
increasing binding power:

 operator      | description                        
---------------|------------------------------------
 `!!`          | disjointness                       
---------------|------------------------------------
 `+`           | set union                          
 `-`           | set difference                     
---------------|------------------------------------
 `*`           | set intersection                   

The associativity rules of `+`, `-`, and `*` are like those of the
arithmetic operators with the same names.  The expression `A !! B`,
whose binding power is the same as equality (but which neither
associates nor chains with equality), says that sets `A` and `B` have
no elements in common, that is, it is equivalent to
```dafny
A * B == {}
```
However, the disjointness operator is chaining, so `A !! B !! C !! D`
means:
```dafny
A * B == {} && (A + B) * C == {} && (A + B + C) * D == {}
```

In addition, for any set `s` of type `set<T>` or `iset<T>` and any
expression `e` of type `T`, sets support the following operations:

 expression          | result type |  description                        
---------------------|:-:|------------------------------------
 `|s|`               | `nat`   | set cardinality 
 `e in s`            | `bool` | set membership 
 `e !in s`           | `bool` | set non-membership 

The expression `e !in s` is a syntactic shorthand for `!(e in s)`.

TODO: Or does the length operator produce an ORDINAL?

## Multisets
````grammar
MultisetType_ = "multiset" [ GenericInstantiation ]
````

A _multiset_ is similar to a set, but keeps track of the multiplicity
of each element, not just its presence or absence.  For any type `T`,
each value of type `multiset<T>` is a map from `T` values to natural
numbers denoting each element's multiplicity.  Multisets in Dafny
are finite, that is, they contain a finite number of each of a finite
set of elements.  Stated differently, a multiset maps only a finite
number of elements to non-zero (finite) multiplicities.

Like sets, multiset membership is determined by equality in the type
`T`, so `multiset<T>` can be used in a non-ghost context only if `T`
is equality supporting.

A multiset can be formed using a _multiset display_ expression, which
is a possibly empty, unordered list of expressions enclosed in curly
braces after the keyword `multiset`.  To illustrate,
```dafny
multiset{}    multiset{0, 1, 1, 2, 3, 5}    multiset{4+2, 1+5, a*b}
```
are three examples of multiset displays.  There is no multiset
comprehension expression.

In addition to equality and disequality, multiset types
support the following relational operations:

 operator          | description                        
-------------------|-----------------------------------
  `<`              | proper multiset subset             
  `<=`             | multiset subset                    
  `>=`             | multiset superset                  
  `>`              | proper multiset superset           

Like the arithmetic relational operators, these operators are
chaining.

Multisets support the following binary operators, listed in order of
increasing binding power:

 operator      | description                        
---------------|------------------------------------
 `!!`          | multiset disjointness              
---------------|------------------------------------
 `+`           | multiset union                     
 `-`           | multiset difference                
---------------|------------------------------------
 `*`           | multiset intersection              

The associativity rules of `+`, `-`, and `*` are like those of the
arithmetic operators with the same names. The `+` operator
adds the multiplicity of corresponding elements, the `-` operator
subtracts them (but 0 is the minimum multiplicity),
and the `*` has multiplicity that is the minimum of the
multiplicity of the operands.

The expression `A !! B`
says that multisets `A` and `B` have no elements in common, that is,
it is equivalent to
```dafny
A * B == multiset{}
```
Like the analogous set operator, `!!` is chaining.

In addition, for any multiset `s` of type `multiset<T>`,
expression `e` of type `T`, and non-negative integer-based numeric
`n`, multisets support the following operations:

 expression          | description                              
---------------------|------------------------------------------
 `|s|`               | multiset cardinality  (result type `nat`)                   
 `e in s`            | multiset membership  (result type `bool`)                     
 `e !in s`           | multiset non-membership   (result type `bool`)
 `s[e]`              | multiplicity of `e` in `s`  (result type `nat`)
 `s[e := n]`         | multiset update (change of multiplicity)  (result type the same as `s`)

The expression `e in s` returns `true` if and only if `s[e] != 0`.
The expression `e !in s` is a syntactic shorthand for `!(e in s)`.
The expression `s[e := n]` denotes a multiset like
`s`, but where the multiplicity of element `e` is `n`.  Note that
the multiset update `s[e := 0]` results in a multiset like `s` but
without any occurrences of `e` (whether or not `s` has occurrences of
`e` in the first place).  As another example, note that
`s - multiset{e}` is equivalent to:
```dafny
if e in s then s[e := s[e] - 1] else s
```

## Sequences
````grammar
SequenceType_ = "seq" [ GenericInstantiation ]
````

For any type `T`, a value of type `seq<T>` denotes a _sequence_ of `T`
elements, that is, a mapping from a finite downward-closed set of natural
numbers (called _indices_) to `T` values.  (Thinking of it as a map,
a sequence is therefore something of a dual of a multiset. TODO: REALLY?)

### Sequence Displays
A sequence can be formed using a _sequence display_ expression, which
is a possibly empty, ordered list of expressions enclosed in square
brackets.  To illustrate,
```dafny
[]        [3, 1, 4, 1, 5, 9, 3]        [4+2, 1+5, a*b]
```
are three examples of sequence displays.  There is no sequence
comprehension expression.

### Sequence Relational Operators
In addition to equality and disequality, sequence types
support the following relational operations:

 operator        | description                        
-----------------|------------------------------------
  <              | proper prefix                      
  <=             | prefix                             

Like the arithmetic relational operators, these operators are
chaining.  Note the absence of `>` and `>=`.

### Sequence Concatenation
Sequences support the following binary operator:

 operator      | description                        
---------------|------------------------------------
 `+`           | concatenation                      

Operator `+` is associative, like the arithmetic operator with the
same name.

### Other Sequence Expressions
In addition, for any sequence `s` of type `seq<T>`, expression `e`
of type `T`, integer-based numeric `i` satisfying `0 <= i < |s|`, and
integer-based numerics `lo` and `hi` satisfying
`0 <= lo <= hi <= |s|`, sequences support the following operations:

 expression         | result type | description                            
 ---------------------|:---:|----------------------------------------
 `|s|`               | `nat` | sequence length                  
 `s[i]`              | `T` |sequence selection                    
 `s[i := e]`         | `seq<T>` | sequence update                       
 `e in s`            | `bool` | sequence membership              
 `e !in s`           | `bool` | sequence non-membership                
 `s[lo..hi]`         | `seq<T>`| subsequence                            
 `s[lo..]`           | `seq<T>` | drop                                   
 `s[..hi]`           | `seq<T>` | take                                   
 `s[`_slices_`]`   | `seq<T>` | slice                                  
 `multiset(s)`       | `multiset<T>`| sequence conversion to a `multiset<T>` 

Expression `s[i := e]` returns a sequence like `s`, except that the
element at index `i` is `e`.  The expression `e in s` says there
exists an index `i` such that `s[i] == e`.  It is allowed in non-ghost
contexts only if the element type `T` is equality supporting.
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
integer-based numeric, whose sum is no greater than `|s|`.  If there
are _k_ colons, the operation produces _k + 1_ consecutive subsequences
from `s`, each of the length indicated by the corresponding length
designator, and returns these as a sequence of
sequences.[^fn-slice-into-tuple] If _slices_ is terminated by a
colon, then the length of the last slice extends until the end of `s`,
that is, its length is `|s|` minus the sum of the given length
designators.  For example, the following equalities hold, for any
sequence `s` of length at least `10`:
```dafny
var t := [3.14, 2.7, 1.41, 1985.44, 100.0, 37.2][1:0:3];
assert |t| == 3 && t[0] == [3.14] && t[1] == [];
assert t[2] == [2.7, 1.41, 1985.44];
var u := [true, false, false, true][1:1:];
assert |u| == 3 && u[0][0] && !u[1][0] && u[2] == [false, true];
assert s[10:][0] == s[..10];
assert s[10:][1] == s[10..];
```

[^fn-slice-into-tuple]:  Now that Dafny supports built-in tuples, the
    plan is to change the sequence slice operation to return not a
    sequence of subsequences, but a tuple of subsequences. TODO: But as a sequence of subsequences one can iterate over them.

The operation `multiset(s)` yields the multiset of elements of
sequence `s`.  It is allowed in non-ghost contexts only if the element
type `T` is equality supporting.

### Strings
````grammar
StringType_ = "string"
````

A special case of a sequence type is `seq<char>`, for which Dafny
provides a synonym: `string`.  Strings are like other sequences, but
provide additional syntax for sequence display expressions, namely
_string literals_.  There are two forms of the syntax for string
literals:  the _standard form_ and the _verbatim form_.

String literals of the standard form are enclosed in double quotes, as
in `"Dafny"`.  To include a double quote in such a string literal,
it is necessary to use an escape sequence.  Escape sequences can also
be used to include other characters.  The supported escape sequences
are the same as those for character literals, see Section [#sec-characters].
For example, the Dafny expression `"say \"yes\""` represents the
string `'say "yes"'`.
The escape sequence for a single quote is redundant, because
`"\'"` and `"\'"` denote the same
string---both forms are provided in order to support the same
escape sequences as do character literals.

String literals of the verbatim form are bracketed by
`@"` and `"]`, as in `@"Dafny"`.  To include
a double quote in such a string literal, it is necessary to use the
escape sequence `\"\"`, that is, to write the character
twice.  In the verbatim form, there are no other escape sequences.
Even characters like newline can be written inside the string literal
(hence spanning more than one line in the program text).

For example, the following three expressions denote the same string:
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

## Finite and Infinite Maps
````grammar
FiniteMapType_ = "map" [ GenericInstantiation ]
InfiniteMapType_ = "imap" [ GenericInstantiation ]
````

For any types `T` and `U`, a value of type `map<T,U>` denotes a
_(finite) map_
from `T` to `U`.  In other words, it is a look-up table indexed by
`T`.  The _domain_ of the map is a finite set of `T` values that have
associated `U` values.  Since the keys in the domain are compared
using equality in the type `T`, type `map<T,U>` can be used in a
non-ghost context only if `T` is equality supporting.

Similarly, for any types `T` and `U`, a value of type `imap<T,U>`
denotes a _(possibly) infinite map_.  In most regards, `imap<T,U>` is
like `map<T,U>`, but a map of type `imap<T,U>` is allowed to have an
infinite domain.

A map can be formed using a _map display_ expression (see ``MapDisplayExpr``),
which is a possibly empty, ordered list of _maplets_, each maplet having the
form `t := u` where `t` is an expression of type `T` and `u` is an
expression of type `U`, enclosed in square brackets after the keyword
`map`.  To illustrate,
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
explained in section [#sec-map-comprehension-expression].

[^fn-map-display]: This is likely to change in the future to disallow
    multiple occurrences of the same key.

For any map `fm` of type `map<T,U>`,
any map `m` of type `map<T,U>` or `imap<T,U>`,
any expression `t` of type `T`,
any expression `u` of type `U`, and any `d` in the domain of `m` (that
is, satisfying `d in m`), maps support the following operations:

 expression      | result type     | description                        
 ---------------|:---:|------------------------------------
 `|fm|`              | `nat` | map cardinality                    
 `m[d]`              | `U` | map selection                      
 `m[t := u]`    | `(i)map<T,U>`      | map update                         
 `t in m`           | `bool`  | map domain membership              
 `t !in m`         | `bool`   | map domain non-membership          
 `fm.Keys`         | `set<T>`   | the domain of fm, that is, the set of T values used as keys           
 `fm.Values`     | `set<U>`     | the range of fm, that is, the set  of U values present in the map   
 `fm.Items`       | `set<(T,U)>`    | set of pairs (t,u) of key-value associations in the map           

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
associated with the same value.

[^fn-map-membership]: This is likely to change in the future as
    follows:  The `in` and `!in` operations will no longer be
    supported on maps, with `x in m` replaced by `x in m.Keys`,
and similarly for `!in`.

Here is a small example, where a map `cache` of type `map<int,real>`
is used to cache computed values of Joule-Thomson coefficients for
some fixed gas at a given temperature:
```dafny
if K in cache {  // check if temperature is in domain of cache
  coeff := cache[K];  // read result in cache
} else {
  coeff := ComputeJouleThomsonCoefficient(K);  // do expensive computation
  cache := cache[K := coeff];  // update the cache
}
```

# Types that stand for other types
````grammar
SynonymTypeDecl =
  ( SynonymTypeDefinition_ | OpaqueTypeDefinition_ ) [ ";" ]
````
It is sometimes useful to know a type by several names or to treat a
type abstractly. Synonym and opaque types serve this purpose.

## Type synonyms
````grammar
SynonymTypeDefinition_ =
  "type" { Attribute } SynonymTypeName [ GenericParameters ] "=" Type
````

A _type synonym_ declaration:
```dafny
type Y<T> = G
```
declares `Y<T>` to be a synonym for the type `G`.  Here, `T` is a
nonempty list of type parameters (each of which is optionally
designated with the suffix `(==)`), which can be used as free type
variables in `G`.  If the synonym has no type parameters, the "`<T>`"
is dropped.  In all cases, a type synonym is just a synonym.  That is,
there is never a difference, other than possibly in error messages
produced, between `Y<T>` and `G`.

For example, the names of the following type synonyms may improve the
readability of a program:
```dafny
type Replacements<T> = map<T,T>
type Vertex = int
```

As already described in Section [#sec-strings], `string` is a built-in
type synonym for `seq<char>`, as if it would have been declared as
follows:
```dafny
type string = seq<char>
```

## Opaque types
````grammar
OpaqueTypeDefinition_ = "type" { Attribute } SynonymTypeName
  [ "(" "==" ")" ] [ GenericParameters ]
````

A special case of a type synonym is one that is underspecified.  Such
a type is declared simply by:
```dafny
type Y<T>
```
It is known as an _opaque type_.  Its definition can be revealed in a
refining module.  To indicate that `Y` designates an
equality-supporting type, "`(==)`" can be written immediately
following the name "`Y`".

For example, the declarations
```dafny
type T
function F(t: T): T
```
can be used to model an uninterpreted function `F` on some
arbitrary type `T`.  As another example,
```dafny
type Monad<T>
```
can be used abstractly to represent an arbitrary parameterized monad.


# Class Types

````grammar
ClassDecl = "class" { Attribute } ClassName [ GenericParameters ]
  ["extends" Type {"," Type} ]
  "{" { { DeclModifier } ClassMemberDecl(moduleLevelDecl: false) } "}"

ClassMemberDecl(moduleLevelDecl) =
  ( FieldDecl | FunctionDecl |
    MethodDecl(isGhost: ("ghost" was present),
               allowConstructor: !moduleLevelDecl)
  )
````
The ``ClassMemberDecl`` parameter `moduleLevelDecl` will be true if
the member declaration is at the top level or directly within a
module declaration. It will be false for ``ClassMemberDecl``s
that are part of a class or trait declaration. If `moduleLevelDecl` is
false ``FieldDecl``s are not allowed.

A _class_ `C` is a reference type declared as follows:
```dafny
class C<T> extends J1, ..., Jn
{
  \(_members_\)
}
```
where the list of type parameters `T` is optional. The text
"`extends J1, ..., Jn`" is also optional and says that the class extends traits `J1` ... `Jn`.
The members of a class are _fields_, _functions_, and
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
```dafny
class C {
  var f: int
  var x: int
  method Example() returns (b: bool)
  {
    var x: int;
    b := f == this.f;
    b := x + this.x;
  }
}
```
so the method body always assigns `true` to the out-parameter `b`.
However, in this example, `x` and `this.x` are different because 
the field `x` is shadowed by the declaration of the local variable `x`.
There is no semantic difference between qualified and
unqualified accesses to the same receiver and member.

A `C` instance is created using `new`, for example:
```dafny
c := new C;
```

Note that `new` simply allocates a `C` object and returns a reference
to it; the initial values of its fields are arbitrary values of their
respective types.  Therefore, it is common to invoke a method, known
as an _initialization method_, immediately after creation, for
example:
```dafny
c := new C;
c.InitFromList(xs, 3);
```
When an initialization method has no out-parameters and modifies no
more than `this`, then the two statements above can be combined into
one:
```dafny
c := new C.InitFromList(xs, 3);
```
Note that a class can contain several initialization methods, that
these methods can be invoked at any time, not just as part of a `new`,
and that `new` does not require that an initialization method be
invoked at creation.

A clas can declare special initializing methods called _constructor methods_.
See Section [#sec-method-declarations].

## Field Declarations
````grammar
FieldDecl = "var" { Attribute } FIdentType { "," FIdentType }
````
An ``FIdentType`` is used to declare a field. The field name is either an
identifier (that is not allowed to start with a leading underscore) or
some digits. Digits are used if you want to number your fields, e.g. "0",
"1", etc.
````grammar
FIdentType = ( FieldIdent | digits ) ":" Type
````

A field x of some type T is declared as:
```dafny
var x: T
```

A field declaration declares one or more fields of the enclosing class.
Each field is a named part of the state of an object of that class. A
field declaration is similar to but distinct from a variable declaration
statement. Unlike for local variables and bound variables, the type is
required and will not be inferred.

Unlike method and function declarations, a field declaration
cannot be given at the top level. Fields can be declared in either a
class or a trait. A class that inherits from multiple traits will
have all the fields declared in any of its parent traits.

Fields that are declared as `ghost` can only be used in specifications,
not in code that will be compiled into executable code.

Fields may not be declared static.

`protected` is not allowed for fields.

## Method Declarations
````grammar
MethodDecl(isGhost, allowConstructor) =
 MethodKeyword { Attribute } [ MethodName ]
 (  MethodSignature(isGhost)  | SignatureEllipsis_ )
 MethodSpec [ BlockStmt ]
````
The `isGhost` parameter is true iff the `ghost` keyword
preceded the method declaration.

If the `allowConstructor` parameter is false then
the ``MethodDecl`` must not be a `constructor`
declaration.

````grammar
MethodKeyword = ("method" | "lemma" | "colemma"
                | "inductive" "lemma" | "constructor" )
````
The method keyword is used to specify special kinds of methods
as explained below.

````grammar
MethodSignature(isGhost) =
    [ GenericParameters ]
    Formals(allowGhost: !isGhost)
    [ "returns" Formals(allowGhost: !isGhost) ]
````
A method signature specifies the method generic parameters,
input parameters and return parameters.
The formal parameters are not allowed to have `ghost` specified
if `ghost` was already specified for the method.

````grammar
SignatureEllipsis_ = "..."
````
A ``SignatureEllipsis_`` is used when a method or function is being redeclared
in module that refines another module. In that case the signature is
copied from the module that is being refined. This works because
Dafny does not support method or function overloading, so the
name of the class method uniquely identifies it without the
signature.

````grammar
Formals(allowGhostKeyword) =
  "(" [ GIdentType(allowGhostKeyword)
        { "," GIdentType(allowGhostKeyword) } ] ")"
````
The ``Formals`` specifies the names and types of the method input or
output parameters.

See section [#sec-method-specification] for a description of ``MethodSpec``.

A method declaration adheres to the ``MethodDecl`` grammar above.
Here is an example of a method declaration.

```dafny
method {:att1}{:att2} M<T1, T2>(a: A, b: B, c: C) returns (x: X, y: Y, z: Z)
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
`Body` is a statement that implements the method. `Frame` can be a list
of expressions, each of which is a set of objects or a single object, the
latter standing for the singleton set consisting of that one object. The
method’s frame is the union of these sets, plus the set of objects
allocated by the method body. For example, if `c` and `d` are parameters
of a class type `C`, then

```dafny
modifies {c, d}

modifies {c} + {d}

modifies c, {d}

modifies c, d
```

all mean the same thing.

A method can be declared as ghost by preceding the declaration with the
keyword `ghost` and as static by preceding the declaration withg the keyword `static`.
The default is non-static (i.e., instance) and non-ghost. An instancemethod has an implicit receiver parameter, `this`. 
A static method M in a class C can be invoked by `C.M(…)`.

In a class, a method can be declared to be a constructor method by
replacing the keyword `method` with the keyword `constructor`. A constructor
can only be called at the time an object is allocated (see
object-creation examples below), and for a class that contains one or
more constructors, object creation must be done in conjunction with a
call to a constructor.

An ordinary method is declared with the `method` keyword.
Section [#sec-constructors] explains methods that instead use the
`constructor` keyword. Section [#sec-lemmas] discusses methods that are
declared with the `lemma` keyword. Methods declared with the `inductive`
`lemma` keywords are discussed later in the context of inductive
predicates (see [#sec-inductive-datatypes]). Methods declared with the
`colemma` keyword are discussed later in the context of co-inductive
types, in section [#sec-colemmas].

A method without a body is _abstract_. A method is allowed to be
abstract under the following circumstances:

* It contains an `{:axiom}` attribute
* It contains an `{:imported}` attribute
* It contains a `{:decl}` attribute
* It is a declaration in an abstract module.
Note that when there is no body, Dafny assumes that the *ensures*
clauses are true without proof. (TODO: `:extern` attribute?)

### Constructors
To write structured object-oriented programs, one often relies on 
objects being constructed only in certain ways.  For this purpose, Dafny
provides _constructor (method)s_, which are a restricted form of
initialization methods.  A constructor is declared with the keyword
`constructor` instead of `method`.  
When a class contains a
constructor, every call to `new` for a class must be accompanied
by a call to one of its constructors.  Moreover, a constructor
cannot be called at other times, only during object creation.  Other
than these restrictions, there is no semantic difference between using
ordinary initialization methods and using constructors. Classes may
declare no constructors or one or more constructors.

#### Classes with no explicit constructors

A class that declares no constructors has a default constructor created 
for it. This constructor is called with the syntax
```dafny
c := new C;
```
This constructor simply initializes the fields of the class.
The declaration of a const field may include an initializer, that is, a right-hand side (RHS) that specifies the constant's value. 
The RHS of a const field may depend on other constant fields, but circular dependencies are not allowed.

This constructor sets each class field to an arbitrary value
of the field's type if the field declaration has no initializer 
and to the value of the initializer expression if it does declare an initializer. 
For the purposes of proving Dafny programs
correct, assigning an arbitrary initial value means that the program must 
be correct for any initial value. Compiled, executable versions of the program
may use a specific initial value 
(for example, but not necessarily, a zero-equivalent or a declared _witness_ value for the type).

#### Classes with one or more constructors
 
When one or more constructors are explicitly declared, they are named, 
which promotes using names like `InitFromList` above.
Constructors must have distinct names, even if their signatures are different.
Many classes have just
one constructor or have a typical constructor.  Therefore, Dafny
allows one _anonymous constructor_, that is, a constructor whose name
is essentially "".  For example:
```dafny
class Item {
  constructor I(xy: int) // ...
  constructor (x: int, y: int)
  // ...
}
```
The named constructor is invoked as
```dafny
  i := new Item.I(42);
```
The anonymous constructor is invoked as
```dafny
  m := new Item(45, 29);
```
dropping the "`.`".

#### Two-phase constructors

The body of a constructor contains two sections, 
an initialization phase and a post-initialization phase, separated by a `new;` statement.
If there is no `new;` statement, the entire body is the initialization phase. 
The initialization phase is intended to initialize field variables. 
In this phase, uses of the object reference `this` are restricted;
a program may use `this`

 - as the receiver on the LHS, 
 - as the entire RHS of an assignment to a field of `this`, 
 - and as a member of a set on the RHS that is being assigned to a field of `this`.

Furthermore, `const` fields may only be assigned to in an initialization phase 
(and may be assigned to more than once)
of their enclosing class, and then only if they do not already have an initialization
value in their declaration.

There are no restrictions on expressions or statements in the post-initialization phase. 

### Lemmas
Sometimes there are steps of logic required to prove a program correct,
but they are too complex for Dafny to discover and use on its own. When
this happens, we can often give Dafny assistance by providing a lemma.
This is done by declaring a method with the `lemma` keyword.
Lemmas are implicitly ghost methods and the `ghost` keyword cannot
be applied to them.

For an example, see the `FibProperty` lemma in
Section [#sec-proofs-in-dafny].

See [the Dafny Lemmas tutorial](http://rise4fun.com/Dafny/tutorial/Lemmas)
for more examples and hints for using lemmas.

### Two-state lemmas and functions
TO BE WRITTEN - two-state lemmas; unchanged predicate

## Function Declarations

````grammar
FunctionDecl =
  ( "function" [ "method" ] { Attribute }
    FunctionName
    FunctionSignatureOrEllipsis_(allowGhostKeyword: ("method" present))
  | "predicate" [ "method" ] { Attribute }
    PredicateName
    PredicateSignatureOrEllipsis_(allowGhostKeyword: ("method" present))
  | "inductive" "predicate" { Attribute }
    PredicateName
    PredicateSignatureOrEllipsis_(allowGhostKeyword: false)
  | "copredicate" { Attribute }
    CopredicateName
    PredicateSignatureOrEllipsis_(allowGhostKeyword: false)
  )
  FunctionSpec [ FunctionBody ]

FunctionSignatureOrEllipsis_(allowGhostKeyword) =
    FunctionSignature_ | SignatureEllipsis_
FunctionSignature_(allowGhostKeyword) =
    [ GenericParameters ] Formals(allowGhostKeyword) ":" Type

PredicateSignatureOrEllipsis_(allowGhostKeyword) =
    PredicateSignature_(allowGhostKeyword) | SignatureEllipsis_
PredicateSignature_(allowGhostKeyword) =
    [ GenericParameters ] Formals(allowGhostKeyword)

FunctionBody = "{" Expression(allowLemma: true, allowLambda: true) "}"
````
In the above productions, `allowGhostKeyword` is true if the optional
`method` keyword was specified. This allows some of the
formal parameters of a function method to be specified as ghost.

See section [#sec-function-specification] for a description of ``FunctionSpec``.

A Dafny function is a pure mathematical function. It is allowed to
read memory that was specified in its `reads` expression but is not
allowed to have any side effects.

Here is an example function declaration:
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
meets the precondition). The postcondition is usually not needed, since
the body of the function gives the full definition. However, the
postcondition can be a convenient place to declare properties of the
function that may require an inductive proof to establish, such as when
the function is recursive. For example:

````grammar
function Factorial(n: int): int
  requires 0 <= n
  ensures 1 <= Factorial(n)
{
  if n == 0 then 1 else Factorial(n-1) * n
}
````

says that the result of Factorial is always positive, which Dafny
verifies inductively from the function body.

By default, a function is ghost, and cannot be called from non-ghost
code. To make it non-ghost, replace the keyword function with the two
keywords "`function method`".

Like methods, functions can be either _instance_ *(which they are be default) or
_static_ (when the function declaration contains the keyword `static`).
An instance function, but not a static function, has an implicit receiver parameter, `this`.  A static function `F` in a class `C` can be invoked
by `C.F(…)`. This can give a convenient way to declare a number of helper
functions in a separate class.

As for methods, a ``SignatureEllipsis_`` is used when declaring
a function in a module refinement. For example, if module `M0` declares
function `F`, a module `M1` can be declared to refine `M0` and
`M1` can then refine `F`. The refinement function, `M1.F` can have
a ``SignatureEllipsis_`` which means to copy the signature form
`M0.F`. A refinement function can furnish a body for a function
(if `M0.F` does not provide one). It can also add `ensures`
clauses. And if `F` is a predicate, it can add conjuncts to
a previously given body.

### Function Transparency
A function is said to be _transparent_ in a location if the
contents of the body of the function is visible at that point.
A function is said to be _opaque_ at a location if it is not
transparent. However the ``FunctionSpec`` of a function
is always available.

A function is usually transparent up to some unrolling level (up to
1, or maybe 2 or 3). If its arguments are all literals it is
transparent all the way.

But the transparency of a function is affected by the following:

* whether the function was declared to be protected, and
* whether the function was given the `{:opaque}` attribute (as explained
in Section [#sec-opaque]).

The following table summarizes where the function is transparent.
The module referenced in the table is the module in which the
function is defined.

 Protected? | `{:opaque}`? | Transparent Inside Module | Transparent Outside Module
:----------:|:------------:|:-----------:|:-----------:
 N          | N            | Y           | Y           
 Y          | N            | Y           | N           
 N          | Y            | N           | N           

When `{:opaque}` is specified for function `g`, `g` is opaque,
however the lemma `reveal_g` is available to give the semantics
of `g` whether in the defining module or outside.

It currently is not allowed to have both `protected` and
`{:opaque}` specified for a function.

### Predicates
A function that returns a `bool` result is called a _predicate_. As an
alternative syntax, a predicate can be declared by replacing the `function`
keyword with the `predicate` keyword and omitting a declaration of the
return type.

### Inductive Predicates and Lemmas
See section [#sec-friendliness] for descriptions
of inductive predicates and lemmas.

# Trait Types
````grammar
TraitDecl = "trait" { Attribute } TraitName [ GenericParameters ]
  "{" { { DeclModifier } ClassMemberDecl(moduleLevelDecl: false) } "}"
````

A _trait_ is an abstract superclass, similar to an "interface" or
"mixin".  Traits are new to Dafny and are likely to evolve for a
while.

The declaration of a trait is much like that of a class:
```dafny
trait J
{
  _members_
}
```
where _members_ can include fields, functions, methods and declarations of nested traits, but
no constructor methods.  The functions and methods are allowed to be
declared `static`.

A reference type `C` that extends a trait `J` is assignable to `J`, but
not the other way around.  The members of `J` are available as members
of `C`.  A member in `J` is not allowed to be redeclared in `C`,
except if the member is a non-`static` function or method without a
body in `J`.  By doing so, type `C` can supply a stronger
specification and a body for the member.

`new` is not allowed to be used with traits.  Therefore, there is no
object whose allocated type is a trait.  But there can of course be
objects of a class `C` that implements a trait `J`, and a reference to
such a `C` object can be used as a value of type `J`.

As an example, the following trait represents movable geometric shapes:
```dafny
trait Shape
{
  function method Width(): real
    reads this
  method Move(dx: real, dy: real)
    modifies this
  method MoveH(dx: real)
    modifies this
  {
    Move(dx, 0.0);
  }
}
```
Members `Width` and `Move` are _abstract_ (that is, body-less) and can
be implemented differently by different classes that extend the trait.
The implementation of method `MoveH` is given in the trait and thus
gets used by all classes that extend `Shape`.  Here are two classes
that each extends `Shape`:
```dafny
class UnitSquare extends Shape
{
  var x: real, y: real
  function method Width(): real {  // note the empty reads clause
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
  {
    xSE - xNW
  }
  method Move(dx: real, dy: real)
    modifies this
  {
    xNW, yNW, xSE, ySE := xNW + dx, yNW + dy, xSE + dx, ySE + dy;
  }
}
```
Note that the classes can declare additional members, that they supply
implementations for the abstract members of the trait,
that they repeat the member signatures, and that they are responsible
for providing their own member specifications that both strengthen the
corresponding specification in the trait and are satisfied by the
provided body.
Finally, here is some code that creates two class instances and uses
them together as shapes:
```dafny
var myShapes: seq<Shape>;
var A := new UnitSquare;
myShapes := [A];
var tri := new LowerRightTriangle;
// myShapes contains two Shape values, of different classes
myShapes := myShapes + [tri];
// move shape 1 to the right by the width of shape 0
myShapes[1].MoveH(myShapes[0].Width());
```

# Array Types
````grammar
ArrayType_ = arrayToken [ GenericInstantiation ]
````

Dafny supports mutable fixed-length _array types_ of any positive
dimension.  Array types are (heap-based) reference types.

## One-dimensional arrays

A one-dimensional array of `n` `T` elements is created as follows:
```dafny
a := new T[n];
```
The initial values of the array elements are arbitrary values of type
`T`.
The length of an array is retrieved using the immutable `Length`
member.  For example, the array allocated above satisfies:
```dafny
a.Length == n
```
Once an array is allocated, its length cannot be changed.

For any integer-based numeric `i` in the range `0 <= i < a.Length`,
the _array selection_ expression `a[i]` retrieves element `i` (that
is, the element preceded by `i` elements in the array).  The
element stored at `i` can be changed to a value `t` using the array
update statement:
```dafny
a[i] := t;
```

Caveat: The type of the array created by `new T[n]` is
`array<T>`.  A mistake that is simple to make and that can lead to
befuddlement is to write `array<T>` instead of `T` after `new`.
For example, consider the following:
```dafny
var a := new array<T>;
var b := new array<T>[n];
var c := new array<T>(n);  // resolution error
var d := new array(n);  // resolution error
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
may be still found can be expressed as follows:
```dafny
key !in a[..lo] && key !in a[hi..]
```
Another use is to say that a certain range of array elements have not
been changed since the beginning of a method:
```dafny
a[lo..hi] == old(a[lo..hi])
```
or since the beginning of a loop:
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
```dafny
multiset(a[..]) == multiset(old(a[..]))
```

## Multi-dimensional arrays

An array of 2 or more dimensions is mostly like a one-dimensional
array, except that `new` takes more length arguments (one for each
dimension), and the array selection expression and the array update
statement take more indices.  For example:
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
holds of the array created above:
```dafny
matrix.Length0 == m && matrix.Length1 == n
```
Higher-dimensional arrays are similar (`Length0`, `Length1`,
`Length2`, ...).  The array selection expression and array update
statement require that the indices are in bounds.  For example, the
swap statement above is well-formed only if:
```dafny
0 <= i < matrix.Length0 && 0 <= j < matrix.Length1 &&
0 <= x < matrix.Length0 && 0 <= y < matrix.Length1
```

In contrast to one-dimensional arrays, there is no operation to
convert stretches of elements from a multi-dimensional array to a
sequence.

# Type `object`
````grammar
ObjectType_ = "object"
````

There is a built-in trait `object` that is like a supertype of all
reference types.[^fn-object-trait] Every class automatically extends
object and so does every user-defined trait. The purpose of type `object`
is to enable a uniform treatment of _dynamic frames_. In particular, it
is useful to keep a ghost field (typically named `Repr` for
"representation") of type `set<object>`.

TODO: what fields, methjods, functions does `object` have?

[^fn-object-trait]: The current compiler restriction that `object` cannot
    be used as a type parameter needs to be removed.

# Iterator types
````grammar
IteratorDecl = "iterator" { Attribute } IteratorName
  ( [ GenericParameters ]
    Formals(allowGhostKeyword: true)
    [ "yields" Formals(allowGhostKeyword: true) ]
  | "..."
  )
  IteratorSpec [ BlockStmt ]
````

See section [#sec-iterator-specification] for a description of ``IteratorSpec``.

An _iterator_ provides a programming abstraction for writing code that
iteratively returns elements.  These CLU-style iterators are
_co-routines_ in the sense that they keep track of their own program
counter and control can be transferred into and out of the iterator
body.

An iterator is declared as follows:
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
```dafny
predicate Valid()
constructor (_in-params_)
  modifies this
  ensures Valid()
```
An iterator is created using `new` and this anonymous constructor.
For example, an iterator willing to return ten consecutive integers
from `start` can be declared as follows:
```dafny
iterator Gen(start: int) yields (x: int)
{
  var i := 0;
  while i < 10 {
    x := start + i;
	  yield;
	  i := i + 1;
  }
}
```
An instance of this iterator is created using:
```dafny
iter := new Gen(30);
```

The predicate `Valid()` says when the iterator is in a state where one
can attempt to compute more elements.  It is a postcondition of the
constructor and occurs in the specification of the `MoveNext` member:
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
```dafny
var start: int
```
The yield-parameters also result in members of the iterator class:
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
```dafny
ghost var xs: seq<int>
```
These history fields are changed automatically by `MoveNext`, but are
not assignable by user code.

Finally, the iterator class contains some special fields for use in
specifications.  In particular, the iterator specification is
recorded in the following immutable fields:
```dafny
ghost var _reads: set<object>
ghost var _modifies: set<object>
ghost var _decreases0: T0
ghost var _decreases1: T1
// ...
```
where there is a `_decreases(_i_): T(_i_)` field for each
component of the iterator's `decreases`
clause.[^fn-iterator-field-names]
In addition, there is a field:
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
    _n_-tuple. Thse changes may be incorporated into a future version
    of Dafny.

Note, in the precondition of the iterator, which is to hold upon
construction of the iterator, the in-parameters are indeed
in-parameters, not fields of `this`.

It is regrettably tricky to use iterators. The language really
ought to have a `foreach` statement to make this easier.
Here is an example showing a definition and use of an iterator.

```dafny
iterator Iter<T>(s: set<T>) yields (x: T)
  yield ensures x in s && x !in xs[..|xs|-1];
  ensures s == set z | z in xs;
{
  var r := s;
  while (r != {})
    invariant forall z :: z in xs ==> x !in r;  // r and xs are disjoint
    invariant s == r + set z | z in xs;
  {
    var y :| y in r;
    r, x := r - {y}, y;
    yield;
    assert y == xs[|xs|-1];  // needed as a lemma to prove loop invariant
  }
}

method UseIterToCopy<T>(s: set<T>) returns (t: set<T>)
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

<!--
# Async-task types

Another experimental feature in Dafny that is likely to undergo some
evolution is _asynchronous methods_.  When an asynchronous method is
called, it does not return values for the out-parameters, but instead
returns an instance of an _async-task type_.  An asynchronous method
declared in a class `C` with the following signature:
```dafny
async method AM<T>(\(_in-params_\)) returns (\(_out-params_\))
```
also gives rise to an async-task type `AM<T>` (outside the enclosing
class, the name of the type needs the qualification `C.AM<T>`).  The
async-task type is a reference type and can be understood as a class
with various members, a simplified version of which is described next.

Each in-parameter `x` of type `X` of the asynchronous method gives
rise to a immutable ghost field of the async-task type:
```dafny
ghost var x: X;
```
Each out-parameter `y` of type `Y` gives rise to a field
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

# Function types

````grammar
Type = DomainType "->" Type
````

Functions are first-class values in Dafny.  Function types have the form
`(T) -> U` where `T` is a comma-delimited list of types and `U` is a
type.  `T` is called the function's _domain type(s)_ and `U` is its
_range type_.  For example, the type of a function
```dafny
function F(x: int, b: bool): real
```
is `(int, bool) -> real`.  Parameters are not allowed to be ghost.

To simplify the appearance of the basic case where a function's
domain consist of a list of exactly one non-function, non-tuple type, the parentheses around
the domain type can be dropped in this case, as in `T -> U`.
This innocent simplification requires additional explanation in the
case where that one type is a tuple type, since tuple types are also
written with enclosing parentheses.
If the function takes a single argument that is a tuple, an additional
set of parentheses is needed.  For example, the function
```dafny
function G(pair: (int, bool)): real
```
has type `((int, bool)) -> real`.  Note the necessary double
parentheses.  Similarly, a function that takes no arguments is
different from one that takes a 0-tuple as an argument.  For instance,
the functions
```dafny
function NoArgs(): real
function Z(unit: ()): real
```
have types `() -> real` and `(()) -> real`, respectively.

The function arrow, `->`, is right associative, so `A -> B -> C` means
`A -> (B -> C)`.  The other association requires explicit parentheses:
`(A -> B) -> C`.

Note that the receiver parameter of a named function is not part of
the type.  Rather, it is used when looking up the function and can
then be thought of as being captured into the function definition.
For example, suppose function `F` above is declared in a class `C` and
that `c` references an object of type `C`; then, the following is type
correct:
```dafny
var f: (int, bool) -> real := c.F;
```
whereas it would have been incorrect to have written something like:
```dafny
var f': (C, int, bool) -> real := F;  // not correct
```

In addition to its type signature, each function value has three properties,
described next.

Every function implicitly takes the heap as an argument.  No function
ever depends on the _entire_ heap, however.  A property of the
function is its declared upper bound on the set of heap locations it
depends on for a given input.  This lets the verifier figure out that
certain heap modifications have no effect on the value returned by a
certain function.  For a function `f: T -> U` and a value `t` of type
`T`, the dependency set is denoted `f.reads(t)` and has type
`set<object>`.

The second property of functions stems from the fact that every function
is potentially _partial_. In other words, a property of a function is its
_precondition_. For a function `f: T -> U`, the precondition of `f` for a
parameter value `t` of type `T` is denoted `f.requires(t)` and has type
`bool`.

The third property of a function is more obvious---the function's
body.  For a function `f: T -> U`, the value that the function yields
for an input `t` of type `T` is denoted `f(t)` and has type `U`.

Note that `f.reads` and `f.requires` are themselves functions.
Suppose `f` has type `T -> U` and `t` has type `T`.  Then, `f.reads`
is a function of type `T -> set<object>` whose `reads` and `requires`
properties are:
```dafny
f.reads.reads(t) == f.reads(t)
f.reads.requires(t) == true
```
`f.requires` is a function of type `T -> bool` whose `reads` and
`requires` properties are:
```dafny
f.requires.reads(t) == f.reads(t)
f.requires.requires(t) == true
```

Dafny also support anonymous functions by means of
_lambda expressions_. See section [#sec-lambda-expressions].

# Algebraic Datatypes

Dafny offers two kinds of algebraic datatypes, those defined
inductively and those defined co-inductively.  The salient property of
every datatype is that each value of the type uniquely identifies one
of the datatype's constructors and each constructor is injective in
its parameters.

````grammar
DatatypeDecl = ( InductiveDatatypeDecl | CoinductiveDatatypeDecl )
````

## Inductive datatypes

````grammar
InductiveDatatypeDecl_ = "datatype" { Attribute } DatatypeName [ GenericParameters ]
  "=" [ "|" ] DatatypeMemberDecl { "|" DatatypeMemberDecl } [ ";" ]
DatatypeMemberDecl = { Attribute } DatatypeMemberName [ FormalsOptionalIds ]
````

The values of inductive datatypes can be seen as finite trees where
the leaves are values of basic types, numeric types, reference types,
co-inductive datatypes, or function types.  Indeed, values of
inductive datatypes can be compared using Dafny's well-founded
`<` ordering.

An inductive datatype is declared as follows:
```dafny
datatype D<T> = (_Ctors_)
```
where _Ctors_ is a nonempty `|`-separated list of
_(datatype) constructors_ for the datatype.  Each constructor has the
form:
```dafny
C(_params_)
```
where _params_ is a comma-delimited list of types, optionally
preceded by a name for the parameter and a colon, and optionally
preceded by the keyword `ghost`.  If a constructor has no parameters,
the parentheses after the constructor name may be omitted.  If no
constructor takes a parameter, the type is usually called an
_enumeration_; for example:
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
```dafny
datatype List<T> = Nil | Cons(head: T, tail: List<T>)
```
the following holds:
```dafny
Cons(5, Nil).Cons? && Cons(5, Nil).head == 5
```
Note that the expression
```dafny
Cons(5, Nil).tail.head
```
is not well-formed, since `Cons(5, Nil).tail` does not satisfy
`Cons?`.

A constructor can have the same name as
the enclosing datatype; this is especially useful for
single-constructor datatypes, which are often called
_record types_.  For example, a record type for black-and-white pixels
might be represented as follows:
```dafny
datatype Pixel = Pixel(x: int, y: int, on: bool)
```

To call a constructor, it is usually necessary only to mention the
name of the constructor, but if this is ambiguous, it is always
possible to qualify the name of constructor by the name of the
datatype.  For example, `Cons(5, Nil)` above can be written
```dafny
List.Cons(5, List.Nil)
```

As an alternative to calling a datatype constructor explicitly, a
datatype value can be constructed as a change in one parameter from a
given datatype value using the _datatype update_ expression.  For any
`d` whose type is a datatype that includes a constructor `C` that has
a parameter (destructor) named `f` of type `T`, and any expression `t`
of type `T`,
```dafny
d.(f := t)
```
constructs a value like `d` but whose `f` parameter is `t`.  The
operation requires that `d` satisfies `C?`.  For example, the
following equality holds:
```dafny
Cons(4, Nil).(tail := Cons(3, Nil)) == Cons(4, Cons(3, Nil))
```

The datatype update expression also accepts multiple field
names, provided these are distinct. For example, a node of some
inductive datatype for trees may be updated as follows:

```dafny
node.(left := L, right := R)
```

## Tuple types
````grammar
TupleType_ = "(" [ Type { "," Type } ] ")"
````

Dafny builds in record types that correspond to tuples and gives these
a convenient special syntax, namely parentheses.  For example, what
might have been declared as:
```dafny
datatype Pair<T,U> = Pair(0: T, 1: U)
```
Dafny provides as the type `(T, U)` and the constructor `(t, u)`, as
if the datatype's name were "" and its type arguments are given in
round parentheses, and as if the constructor name were "".  Note that
the destructor names are `0` and `1`, which are legal identifier names
for members.  For example, showing the use of a tuple destructor, here
is a property that holds of 2-tuples (that is, _pairs_):
```dafny
(5, true).1 == true
```

Dafny declares _n_-tuples where _n_ is 0 or 2 or more.  There are no
1-tuples, since parentheses around a single type or a single value have
no semantic meaning.  The 0-tuple type, `()`, is often known as the
_unit type_ and its single value, also written `()`, is known as _unit_.

## Co-inductive datatypes

````grammar
CoinductiveDatatypeDecl_ = "codatatype" { Attribute } DatatypeName [ GenericParameters ]
  "=" DatatypeMemberDecl { "|" DatatypeMemberDecl } [ ";" ]
````

Whereas Dafny insists that there is a way to construct every inductive
datatype value from the ground up, Dafny also supports
_co-inductive datatypes_, whose constructors are evaluated lazily and
hence allows infinite structures.  A co-inductive datatype is declared
using the keyword `codatatype`; other than that, it is declared and
used like an inductive datatype.

For example,
```dafny
codatatype IList<T> = Nil | Cons(head: T, tail: IList<T>)
codatatype Stream<T> = More(head: T, tail: Stream<T>)
codatatype Tree<T> = Node(left: Tree<T>, value: T, right: Tree<T>)
```
declare possibly infinite lists (that is, lists that can be either
finite or infinite), infinite streams (that is, lists that are always
infinite), and infinite binary trees (that is, trees where every
branch goes on forever), respectively.

The paper [Co-induction Simply], by Leino and
Moskal[@LEINO:Dafny:Coinduction], explains Dafny's implementation and
verification of co-inductive types. We capture the key features from that
paper in this section but the reader is referred to that paper for more
complete details and to supply bibliographic references that are
omitted here.

Mathematical induction is a cornerstone of programming and program
verification. It arises in data definitions (e.g., some algebraic data
structures can be described using induction), it underlies program
semantics (e.g., it explains how to reason about finite iteration and
recursion), and it is used in proofs (e.g., supporting lemmas about
data structures use inductive proofs). Whereas induction deals with
finite things (data, behavior, etc.), its dual, co-induction, deals with
possibly infinite things. Co-induction, too, is important in programming
and program verification: it arises in data definitions (e.g., lazy
data structures), semantics (e.g., concurrency), and proofs (e.g.,
showing refinement in a co-inductive big-step semantics). It is thus
desirable to have good support for both induction and co-induction in a
system for constructing and reasoning about programs.

Co-datatypes and co-recursive functions make it possible to use lazily
evaluated data structures (like in Haskell or Agda). Co-predicates,
defined by greatest fix-points, let programs state properties of such
data structures (as can also be done in, for example, Coq). For the
purpose of writing co-inductive proofs in the language, we introduce
co-lemmas. Ostensibly, a co-lemma invokes the co-induction hypothesis
much like an inductive proof invokes the induction hypothesis. Underneath
the hood, our co-inductive proofs are actually approached via induction:
co-lemmas provide a syntactic veneer around this approach.

The following example gives a taste of how the co-inductive features in
Dafny come together to give straightforward definitions of infinite
matters.
```dafny
// infinite streams
codatatype IStream<T> = ICons(head: T, tail: IStream)

// pointwise product of streams
function Mult(a: IStream<int>, b: IStream<int>): IStream<int>
{ ICons(a.head * b.head, Mult(a.tail, b.tail)) }

// lexicographic order on streams
copredicate Below(a: IStream<int>, b: IStream<int>)
{ a.head <= b.head && ((a.head == b.head) ==> Below(a.tail, b.tail)) }

// a stream is Below its Square
colemma Theorem_BelowSquare(a: IStream<int>)
ensures Below(a, Mult(a, a))
{ assert a.head <= Mult(a, a).head;
  if a.head == Mult(a, a).head {
    Theorem_BelowSquare(a.tail);
  }
}

// an incorrect property and a bogus proof attempt
colemma NotATheorem_SquareBelow(a: IStream<int>)
  ensures Below(Mult(a, a), a); // ERROR
{
  NotATheorem_SquareBelow(a);
}
```

The example defines a type `IStream` of infinite streams, with constructor `ICons` and
destructors `head` and `tail`. Function `Mult` performs pointwise
multiplication on infinite streams of integers, defined using a
co-recursive call (which is evaluated lazily). Co-predicate `Below` is
defined as a greatest fix-point, which intuitively means that the
co-predicate will take on the value true if the recursion goes on forever
without determining a different value. The co-lemma states the theorem
`Below(a, Mult(a, a))`. Its body gives the proof, where the recursive
invocation of the co-lemma corresponds to an invocation of the
co-induction hypothesis.

The proof of the theorem stated by the first co-lemma lends
itself to the following intuitive reading: To prove that `a` is below
`Mult(a, a)`, check that their heads are ordered and, if the heads are
equal, also prove that the tails are ordered. The second co-lemma states
a property that does not always hold; the verifier is not fooled by the
bogus proof attempt and instead reports the property as unproved.

We argue that these definitions in Dafny are simple enough to level the
playing field between induction (which is familiar) and co-induction
(which, despite being the dual of induction, is often perceived as eerily
mysterious). Moreover, the automation provided by our SMT-based verifier
reduces the tedium in writing co-inductive proofs. For example, it
verifies `Theorem_BelowSquare` from the program text given above— no
additional lemmas or tactics are needed. In fact, as a consequence of the
automatic-induction heuristic in Dafny, the verifier will
automatically verify Theorem_BelowSquare even given an empty body.

Just like there are restrictions on when an _inductive hypothesis_ can be
invoked, there are restrictions on how a _co-inductive_ hypothesis can be
_used_. These are, of course, taken into consideration by Dafny's verifier.
For example, as illustrated by the second co-lemma above, invoking the
co-inductive hypothesis in an attempt to obtain the entire proof goal is
futile. (We explain how this works in section [#sec-colemmas]) Our initial experience
with co-induction in Dafny shows it to provide an intuitive, low-overhead
user experience that compares favorably to even the best of today’s
interactive proof assistants for co-induction. In addition, the
co-inductive features and verification support in Dafny have other
potential benefits. The features are a stepping stone for verifying
functional lazy programs with Dafny. Co-inductive features have also
shown to be useful in defining language semantics, as needed to verify
the correctness of a compiler, so this opens the possibility that
such verifications can benefit from SMT automation.

### Well-Founded Function/Method Definitions
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
```dafny
forall x | P(x) { Lemma(x); }
```
is used to invoke `Lemma(x)` on all `x` for which `P(x)` holds. If
`Lemma(x)` ensures `Q(x)`, then the forall statement establishes
```dafny
forall x :: P(x) ==> Q(x).
```

### Defining Co-inductive Datatypes
Each value of an inductive datatype is finite, in the sense that it can
be constructed by a finite number of calls to datatype constructors. In
contrast, values of a co-inductive datatype, or co-datatype for short,
can be infinite. For example, a co-datatype can be used to represent
infinite trees.

Syntactically, the declaration of a co-datatype in Dafny looks like that
of a datatype, giving prominence to the constructors (following Coq). The
following example defines a co-datatype Stream of possibly
infinite lists.

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
```

`Stream` is a co-inductive datatype whose values are possibly infinite
lists. Function `Up` returns a stream consisting of all integers upwards
of `n` and `FivesUp` returns a stream consisting of all multiples of 5
upwards of `n` . The self-call in `Up` and the first self-call in `FivesUp`
sit in productive positions and are therefore classified as co-recursive
calls, exempt from termination checks. The second self-call in `FivesUp` is
not in a productive position and is therefore subject to termination
checking; in particular, each recursive call must decrease the rank
defined by the `decreases` clause.

Analogous to the common finite list datatype, Stream declares two
constructors, `SNil` and `SCons`. Values can be destructed using match
expressions and statements. In addition, like for inductive datatypes,
each constructor `C` automatically gives rise to a discriminator `C?` and
each parameter of a constructor can be named in order to introduce a
corresponding destructor. For example, if `xs` is the stream
`SCons(x, ys)`, then `xs.SCons?` and `xs.head == x` hold. In contrast
to datatype declarations, there is no grounding check for
co-datatypes—since a codatatype admits infinite values, the type is
nevertheless inhabited.

### Creating Values of Co-datatypes
To define values of co-datatypes, one could imagine a “co-function”
language feature: the body of a “co-function” could include possibly
never-ending self-calls that are interpreted by a greatest fix-point
semantics (akin to a **CoFixpoint** in Coq). Dafny uses a different design:
it offers only functions (not “co-functions”), but it classifies each
intra-cluster call as either _recursive_ or _co-recursive_. Recursive calls
are subject to termination checks. Co-recursive calls may be
never-ending, which is what is needed to define infinite values of a
co-datatype. For example, function `Up(n )` in the preceding example is defined as the
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

### Copredicates
Determining properties of co-datatype values may require an infinite
number of observations. To that end, Dafny provides _co-predicates_
which are function declarations that use the `copredicate` keyword.
Self-calls to a co-predicate need not terminate. Instead, the value
defined is the greatest fix-point of the given recurrence equations.
Continuing the preceding example, the following code defines a
co-predicate that holds for exactly those streams whose payload consists
solely of positive integers. The co-predicate definition implicitly also
gives rise to a corresponding prefix predicate, `Pos#`. The syntax for
calling a prefix predicate sets apart the argument that specifies the
prefix length, as shown in the last line; for this figure, we took the
liberty of making up a coordinating syntax for the signature of the
automatically generated prefix predicate (which is not part of
Dafny syntax).

```dafny
copredicate Pos(s: Stream<int>)
{
  match s
  case SNil => true
  case SCons(x, rest) => x > 0 && Pos(rest)
}
// Automatically generated by the Dafny compiler:
predicate Pos#[_k: nat](s: Stream<int>)
  decreases _k
{ if _k = 0 then true else
  match s
  case SNil => true
  case SCons(x, rest) => x > 0 && Pos#[_k-1](rest)
}
```

Some restrictions apply. To guarantee that the greatest fix-point always
exists, the (implicit functor defining the) co-predicate must be
monotonic. This is enforced by a syntactic restriction on the form of the
body of co-predicates: after conversion to negation normal form (i.e.,
pushing negations down to the atoms), intra-cluster calls of
co-predicates must appear only in _positive_ positions—that is, they must
appear as atoms and must not be negated. Additionally, to guarantee
soundness later on, we require that they appear in _co-friendly_
positions—that is, in negation normal form, when they appear under
existential quantification, the quantification needs to be limited to a
finite range[^fn-copredicate-restriction]. Since the evaluation of a co-predicate might not
terminate, co-predicates are always ghost. There is also a restriction on
the call graph that a cluster containing a co-predicate must contain only
co-predicates, no other kinds of functions.

[^fn-copredicate-restriction]: Higher-order function support in Dafny is
    rather modest and typical reasoning patterns do not involve them, so this
    restriction is not as limiting as it would have been in, e.g., Coq.

A **copredicate** declaration of `P` defines not just a co-predicate, but
also a corresponding _prefix predicate_ `P#`. A prefix predicate is a
finite unrolling of a co-predicate. The prefix predicate is constructed
from the co-predicate by

* adding a parameter _k of type nat to denote the prefix length,

* adding the clause "**decreases** `_k;`" to the prefix predicate (the
  co-predicate itself is not allowed to have a decreases clause),

* replacing in the body of the co-predicate every intra-cluster
  call `Q(args)` to a copredicate by a call `Q#[_k - 1](args)`
  to the corresponding prefix predicate, and then

* prepending the body with `if _k = 0 then true else`.

For example, for co-predicate `Pos`, the definition of the prefix
predicate `Pos#` is as suggested above. Syntactically, the prefix-length
argument passed to a prefix predicate to indicate how many times to
unroll the definition is written in square brackets, as in `Pos#[k](s)`.
In the Dafny grammar this is called a ``HashCall``. The definition of
`Pos#` is available only at clusters strictly higher than that of `Pos`;
that is, `Pos` and `Pos#` must not be in the same cluster. In other
words, the definition of `Pos` cannot depend on `Pos#`.

#### Co-Equality
Equality between two values of a co-datatype is a built-in co-predicate.
It has the usual equality syntax `s == t`, and the corresponding prefix
equality is written `s ==#[k] t`. And similarly for `s != t`
and `s !=#[k] t`.

### Co-inductive Proofs
From what we have said so far, a program can make use of properties of
co-datatypes. For example, a method that declares `Pos(s)` as a
precondition can rely on the stream `s` containing only positive integers.
In this section, we consider how such properties are established in the
first place.

#### Properties About Prefix Predicates
Among other possible strategies for establishing co-inductive properties
we take the time-honored approach of reducing co-induction to
induction. More precisely, Dafny passes to the SMT solver an
assumption `D(P)` for every co-predicate `P`, where:

```dafny
D(P) = ? x • P(x) <==> ? k • P#[k](x)
```

In other words, a co-predicate is true iff its corresponding prefix
predicate is true for all finite unrollings.

In Sec. 4 of the paper [Co-induction Simply] a soundness theorem of such
assumptions is given, provided the co-predicates meet the co-friendly
restrictions. An example proof of `Pos(Up(n))` for every `n > 0` is
here shown:

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
the forall statement to show `? k • Pos#[k](Up(n))`. Finally, the axiom
`D(Pos)` is used (automatically) to establish the co-predicate.


#### Colemmas
As we just showed, with help of the `D` axiom we can now prove a
co-predicate by inductively proving that the corresponding prefix
predicate holds for all prefix lengths `k` . In this section, we introduce
_co-lemma_ declarations, which bring about two benefits. The first benefit
is that co-lemmas are syntactic sugar and reduce the tedium of having to
write explicit quantifications over `k` . The second benefit is that, in
simple cases, the bodies of co-lemmas can be understood as co-inductive
proofs directly. As an example consider the following co-lemma.

```dafny
colemma UpPosLemma(n: int)
  requires n > 0
  ensures Pos(Up(n))
{
  UpPosLemma(n+1);
}
```
This co-lemma can be understood as follows: `UpPosLemma` invokes itself
co-recursively to obtain the proof for `Pos(Up(n).tail)` (since `Up(n).tail`
equals `Up(n+1)`). The proof glue needed to then conclude `Pos(Up(n))` is
provided automatically, thanks to the power of the SMT-based verifier.

#### Prefix Lemmas
To understand why the above `UpPosLemma` co-lemma code is a sound proof,
let us now describe the details of the desugaring of co-lemmas. In
analogy to how a **copredicate** declaration defines both a co-predicate and
a prefix predicate, a **colemma** declaration defines both a co-lemma and
_prefix lemma_. In the call graph, the cluster containing a co-lemma must
contain only co-lemmas and prefix lemmas, no other methods or function.
By decree, a co-lemma and its corresponding prefix lemma are always
placed in the same cluster. Both co-lemmas and prefix lemmas are always
ghosts.

The prefix lemma is constructed from the co-lemma by

* adding a parameter `_k` of type `nat` to denote the prefix length,

* replacing in the co-lemma’s postcondition the positive co-friendly
  occurrences of co-predicates by corresponding prefix predicates,
  passing in `_k` as the prefix-length argument,

* prepending `_k` to the (typically implicit) **decreases** clause of the co-lemma,

* replacing in the body of the co-lemma every intra-cluster call
  `M(args)` to a colemma by a call `M#[_k - 1](args)` to the
  corresponding prefix lemma, and then

* making the body’s execution conditional on `_k != 0`.

Note that this rewriting removes all co-recursive calls of co-lemmas,
replacing them with recursive calls to prefix lemmas. These recursive
call are, as usual, checked to be terminating. We allow the pre-declared
identifier `_k` to appear in the original body of the
co-lemma.[^fn-co-predicate-co-lemma-diffs]

[^fn-co-predicate-co-lemma-diffs]: Note, two places where co-predicates
    and co-lemmas are not analogous are: co-predicates must not make
    recursive calls to their prefix predicates, and co-predicates cannot
    mention _k.

We can now think of the body of the co-lemma as being replaced by a
**forall** call, for every _k_ , to the prefix lemma. By construction,
this new body will establish the colemma’s declared postcondition (on
account of the `D` axiom, and remembering that only the positive
co-friendly occurrences of co-predicates in the co-lemma’s postcondition
are rewritten), so there is no reason for the program verifier to check
it.

The actual desugaring of our co-lemma `UpPosLemma` is in fact the
previous code for the `UpPosLemma` lemma except that `UpPosLemmaK` is
named `UpPosLemma#` and modulo a minor syntactic difference in how the
`k` argument is passed.

In the recursive call of the prefix lemma, there is a proof obligation
that the prefixlength argument `_k - 1` is a natural number.
Conveniently, this follows from the fact that the body has been wrapped
in an `if _k != 0` statement. This also means that the postcondition must
hold trivially when `_k = 0`, or else a postcondition violation will be
reported. This is an appropriate design for our desugaring, because
co-lemmas are expected to be used to establish co-predicates, whose
corresponding prefix predicates hold trivially when `_k = 0`. (To prove
other predicates, use an ordinary lemma, not a co-lemma.)

It is interesting to compare the intuitive understanding of the
co-inductive proof in using a co-lemma with the inductive proof in using
the lemma. Whereas the inductive proof is performing proofs for deeper
and deeper equalities, the co-lemma can be understood as producing the
infinite proof on demand.

# Newtypes
````grammar
NewtypeDecl = "newtype" { Attribute } NewtypeName "="
  ( NumericTypeName [ ":" Type ] "|" Expression(allowLemma: false, allowLambda: true)
  | Type
  )
````

A new numeric type can be declared with the _newtype_
declaration, for example:
```dafny
newtype N = x: M | Q
```
where `M` is a numeric type and `Q` is a boolean expression that can
use `x` as a free variable.  If `M` is an integer-based numeric type,
then so is `N`; if `M` is real-based, then so is `N`.  If the type `M`
can be inferred from `Q`, the "`: M`" can be omitted.  If `Q` is just
`true`, then the declaration can be given simply as:
```dafny
newtype N = M
```
Type `M` is known as the _base type_ of `N`.


A newtype is a numeric type that supports the same operations as its
base type.  The newtype is distinct from and incompatible with other
numeric types; in particular, it is not assignable to its base type
without an explicit conversion.  An important difference between the
operations on a newtype and the operations on its base type is that
the newtype operations are defined only if the result satisfies the
predicate `Q`, and likewise for the literals of the
newtype.[^fn-newtype-design-question]

[^fn-newtype-design-question]: Would it be useful to also
    automatically define `predicate N?(x: M) { Q }`?

For example, suppose `lo` and `hi` are integer-based numerics that
satisfy `0 <= lo <= hi` and consider the following code fragment:
```dafny
var mid := (lo + hi) / 2;
```
If `lo` and `hi` have type `int`, then the code fragment is legal; in
particular, it never overflows, since `int` has no upper bound.  In
contrast, if `lo` and `hi` are variables of a newtype `int32` declared
as follows:
```dafny
newtype int32 = x | -0x80000000 <= x < 0x80000000
```
then the code fragment is erroneous, since the result of the addition
may fail to satisfy the predicate in the definition of `int32`.  The
code fragment can be rewritten as
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

Note that the bound variable `x` in `Q` has type `M`, not `N`.
Consequently, it may not be possible to state `Q` about the `N`
value.  For example, consider the following type of 8-bit 2's
complement integers:
```dafny
newtype int8 = x: int | -128 <= x < 128
```
and consider a variable `c` of type `int8`.  The expression
```dafny
-128 <= c < 128
```
is not well-defined, because the comparisons require each operand to
have type `int8`, which means the literal `128` is checked to be of
type `int8`, which it is not.  A proper way to write this expression
would be to use a conversion operation, described next, on `c` to
convert it to the base type:
```dafny
-128 <= c as int < 128
```

If possible, Dafny compilers will represent values of the newtype using
a native data type for the sake of efficiency. This action can
be inhibited or a specific native data type selected by
using the `{:nativeType}` attribute, as explained in
section [#sec-nativetype].

There is a restriction that the value `0` must be part of every
newtype.[^fn-newtype-zero]

Furthermore, for the compiler to be able to make an appropriate choice of
representation, the constants in the defining expression as shown above must be
known constants at compile-time. They need not be numeric literals; combinations
of basic operations and symbolic constants are also allowed as described 
in [Section: Compile-Time Constants](#sec-compile-time-constants).

[^fn-newtype-zero]: The restriction is due to a current limitation in
    the compiler.  This will change in the future and will also open
    up the possibility for subset types and non-null reference
    types.

## Numeric conversion operations

For every numeric type `N`, there is a conversion function with the
name `as N`.  It is a partial identity function.  It is defined when the
given value, which can be of any numeric type, is a member of the type
converted to.  When the conversion is from a real-based numeric type
to an integer-based numeric type, the operation requires that the
real-based argument have no fractional part.  (To round a real-based
numeric value down to the nearest integer, use the `.Floor` member,
see Section [#sec-numeric-types].)

To illustrate using the example from above, if `lo` and `hi` have type
`int32`, then the code fragment can legally be written as follows:
```dafny
var mid := (lo as int + hi as int) / 2;
```
where the type of `mid` is inferred to be `int`.  Since the result
value of the division is a member of type `int32`, one can introduce
yet another conversion operation to make the type of `mid` be `int32`:
```dafny
var mid := int32(lo as int + hi as int) / 2);
```
If the compiler does specialize the run-time representation for
`int32`, then these statements come at the expense of two,
respectively three, run-time conversions.

The `as N` conversion operation is grammatically a suffix operation like 
`.`_field and array indsexing. Thus the as operawtion binds more tightly than
p[refix or binary operations: `- x as int` is `- (x as int)`; `a + b as int` is `a + (b as int)`.

TODO: Move this section to Expressions?

# Subset types {#sec-subset-types}
TO BE WRITTEN: add `-->` (subset of `~>`), `->` (subset of `-->`), non-null types subset of nullable types

````grammar
SubsetTypeDecl = "type" { Attribute } NewtypeName OptGenericParameters "="
  Ident [ ":" Type ] "|" Expression(allowLemma: false, allowLambda: true)
    [ "witness" Expression(allowLemma: false, allowLambda: true) ]
````

````grammar
NatType_ = "nat"
````

A _subset type_ is a restricted use of an existing type, called
the _base type_ of the subset type.  A subset type is like a
combined use of the base type and a predicate on the base
type.

An assignment from a subset type to its base type is always
allowed.  An assignment in the other direction, from the base type to
a subset type, is allowed provided the value assigned does indeed
satisfy the predicate of the subset type.
(Note, in contrast, assignments between a newtype and its base type
are never allowed, even if the value assigned is a value of the target
type.  For such assignments, an explicit conversion must be used, see
Section [#sec-numeric-conversion-operations].)

Dafny supports a builtin subset type, namely the built-in type `nat`,
whose base type is `int`.[^fn-more-subset-types]  Type `nat`
designates the non-negative subrange of `int`.  A simple example that
puts subset type `nat` to good use is the standard Fibonacci
function:
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
```dafny
function Fib(n: int): int
  requires 0 <= n  // the function argument must be non-negative
  ensures 0 <= Fib(n)  // the function result is non-negative
{
  if n < 2 then n else Fib(n-2) + Fib(n-1)
}
```

TODO: I think the following is false, or at least should be.

Type inference will never infer the type of a variable to be a
subset type.  It will instead infer the type to be the base type
of the subset type.  For example, the type of `x` in
```dafny
forall x :: P(x)
```
will be `int`, even if predicate `P` declares its argument to have
type `nat`.
