
<!-- %check-resolve %default %useHeadings -->

<!-- FILE ./DafnyCore/Resolver/NameResolutionAndTypeInference.cs -->

## **Error: a newtype ('_type_') must be based on some non-reference, non-trait, non-arrow, non-ORDINAL, non-datatype type (got _type_)**

```dafny
datatype D = A | B
newtype T = D
```

In the current definition of the Dafny language, newtypes may only be 
based on numeric types: int and real and subtypes and newtypes based on them.
This may change in the future.

## **Error: newtype constraint must be of type bool (instead got _type_)**

```dafny
newtype T = i: int | i 
```

The expression after the vertical bar must be a boolean condition.
The values of the basetype that satisfy this condition are the members 
of the newtype. This is different than, say, a set comprehension like
`set i: int :: i*2` where the expression after the `::` gives the elements
of the set directly.

## **Error: subset type constraint must be of type bool (instead got _type_)**

```dafny
type T = i: int | i
```

The expression after the vertical bar must be a boolean condition.
The values of the basetype that satisfy this condition are the members 
of the subset type. This is different than, say, a set comprehension like
`set i: int :: i*2` where the expression after the `::` gives the elements
of the set directly.

## **Error: witness expression must have type '_type_' (got '_type_')**

<!-- %check-resolve %options --type-system-refresh=false --general-traits=legacy --general-newtypes=false -->
```dafny
type T = i: int | 100 < i < 102 witness true
```

In some definitions of subset types or newtypes, Dafny needs an example value
to know that the type is not empty. That value is called a `witness` and 
is a specific value that can be proved to be a member of the type.
Since it is a member of the newly defined type, and hence of the basetype,
the witness may not be an expression of some different type.

<!-- 2 instances -->

## **Error: type of unary - must be of a numeric or bitvector type (instead got _type_)**

```dafny
datatype D = A | B
const d := A
const x := -d
```

The unary - (negation) operator acts only on `int`, `real`, and bitvector values
and values of types based on those types.

## **Error: type of 'null' is a reference type, but it is used as _type_**

```dafny
const i: int := null
```

`null` is a literal value (like `true` and `1`) whose type is a reference type.
So it can only be used in contexts that can accept a reference value, such as
assignment to a variable of nullable reference type. Primitive types like
`boolean`, `int`, `real`, `char`, `string`, and datatypes do not have any
value `null` (and there are no types like `string?` or `D?` for a datatype `D`).

## **Error: integer literal used as if it had type _type_**

<!-- TODO -->
_This error is not yet documented._

## **Error: real literal used as if it had type _type_**

<!-- TODO -->
_This error is not yet documented._

## **Error: 'this' is not allowed in a 'static' context**

```dafny
class A {}
method m() {
  var a: A := this;
}
```

As in some other programming languages, `this` in Dafny refers to the object that contains 
the method in which the identifier `this` is used. However, the containing object is
an implicit argument to a method only if it is an _instance_ method, not if it is a
_static_ method; so `this` cannot be used in static methods.

A method in a class is instance by default and static only if it is explicitly
declared so. A method declared at the top-level or as a direct member of a 
module is implicitly static (and cannot be instance). 

## **Error: Identifier does not denote a local variable, parameter, or bound variable: _name_**

<!-- TODO -->
_This error message is not yet documented._

## **Error: Undeclared datatype: _type_**

<!-- TODO - may not be reachable -->
_This error message is not yet documented. Please report any source code that provokes it._

## **Error: The name _type_ ambiguously refers to a type in one of the modules _modules_ (try qualifying the type name with the module name)**

```dafny
module M { type T }
module N { type T }

import opened M
import opened N
const t: T

```

The stated type name has more than one declaration in scope, likely because both have been imported
with `opened`. In that case the name must be qualified to indicate which declaration is intended.

## **Error: Expected datatype: _type_**

<!-- TODO - may not be reachable -->
_This error message is not yet documented. Please report any source code that provokes it._

## **Error: All elements of display must have some common supertype (got _type_, but needed type or type of previous elements is _type_)**

```dafny
const d := [4.0, 6]
```

## **Error: All elements of display must have some common supertype (got _type_, but needed type or type of previous elements is _type_)**

```dafny
const d := map[2 := 3, 4.0 := 6]
```

A map display associates a number of domain values with corresponding range values using the syntax _domain value_ := _range value_. 
All the domain values must have the same type or a common supertype.

## **Error: All elements of display must have some common supertype (got _type_, but needed type or type of previous elements is _type_)**

```dafny
const d := map[2 := 3, 4 := 6.0 ]
```

A map display associates a number of domain values with corresponding range values using the syntax _domain value_ := _range value_. 
All the range values must have the same type or a common supertype.

## **Error: name of module (_name_) is used as a variable**

```dafny
module M {}
const c := M
```

All names in Dafny (except for names of export sets) are in one namespace. Names in different 
scopes can be distinguished by qualification. Names can also be redeclared in a nested scope
with different properties. But if a name is visible, it must be used consistent with its
declaration. So a name declared as a module cannot be used as a variable, even though it is 
usually clear from context where module names are used and where expressions are used.


<!-- 2 instances -->

## **Error: name of type (_type_) is used as a variable**

```dafny
type t = int
method m(i: int) {
  t := i;
}
```

All names in Dafny (except for names of export sets) are in one namespace. Names in different 
scopes can be distinguished by qualification. Names can also be redeclared in a nested scope
with different properties. But if a name is visible, it must be used consistent with its
declaration. So a name declared as a type cannot be used as a variable, even though it is 
usually clear from context where type names are used and where expressions are used.

<!-- 2 instances -->

## **Error: a two-state function can be used only in a two-state context**

<!-- %no-check TODO - fix - incorrect error message for this example -->
```dafny
module M {
  twostate function f(): int
}
const c := M.f()
```

A `twostate` function is a function of two different heaps.
Accordingly it can be used only in situations in which there are two states
in play (that is, a _two-state_ context).  One example is in a postcondition
(_ensures_ clause) where the two states are the states at the beginning and end 
of the method execution. Another two-state context is the body of a method, 
where the states are the pre-state of the method and the current state at the
location of the call. However, contexts outside of a method, such as initializations 
of const declarations, are not two-state contexts.

## **Error: a field must be selected via an object, not just a class name**

<!-- TODO - may not be reachable -->
_This error message is not yet documented. Please report any source code that provokes it._

## **Error: member _name_ in type _type_ does not refer to a field or a function**

<!-- TODO - may not be reachable -->
_This error message is not yet documented. Please report any source code that provokes it._

## **Error: array selection requires an array_n_ (got _type_)**

```dafny
const a: int
const x: ORDINAL
method m() 
{  
  var c := a[0,0];
}
```

The `a[1,2,3]` syntax denotes the selection of an array element of a multi-dimensional array.
So the expression prior to the '[' must have array type with a number of dimensions that
matches the number of index expressions between the left and right brackets.	

## **Error: array selection requires integer- or bitvector-based numeric indices (got _type_ for index _i_)**

```dafny
const a: array2<int>
const c := a['c',0]
```

Multi-dimensional arrays are selected only by integer or bit-vector values.
There is no implicit conversion from characters or reals.
A value of ORDINAL type may be used if it can be proved that the value is
less than the length of the array dimension.
Note that the 'index' in the error message is counted from 0.

## **Error: update requires a sequence, map, or multiset (got _type_)**

```dafny
method m(i: int, s: seq<int>) 
  requires |s| > 100
{
  var ss := i[1 := 10];
}
```

The update syntax provides a way to produce a slightly modified sequence, multiset, or map:
if `s` is a `seq<int>`, then `s[1 := 10]` is a `seq<int>` with the same values at the same positions
as `s`, except that the value at position 1 is now 10. It is important to understand that
these are _value_ types; the original value of `s` is unchanged; rather a new value is
produced as a result of the update expression.
 
## **Error: datatype update expression requires a root expression of a datatype (got _type_)**

```dafny
method m(a: int) 
{  
var c := a.(x := 0);
}
```

The `.(` syntax indicates a _datatype update expression_. The expression before the `.(`
should be a value of some datatype, but Dafny's type inference found it to be something else.

## **Error: non-function expression (of type _type_) is called with parameters**

```dafny
method m(i: int) 
{
  var k := i(9);
}
```

The syntax `f(a,b,c)` is an example of a call of a function or method `f`, with, in this case,
three actual arguments, which must correespond to the formal arguments in the definition of `f`.
This syntax is only legal in an expression if the expression prior to the left parenthesis is a function,
and not something else. It need not be just an identifier; it could be a expression, such
as a lambda expression: `((f:int)=>42)(1)`.

## **Error: wrong number of arguments for function application (function type '_type_' expects _number_, got _number_)**

<!-- %no-check TODO - fix - different error message for this example -->
```dafny
function f(): int { 0 }
const k := f(1,2);
```

This message indicates that in some function call the number of actual arguments does
not match the number of formal parameters (as given in the function definition).
Usually the actuals and formals must match exactly, but Dafny does allow
for optional and named arguments with default values. In those cases, the number of actual
arguments may be less than the number of formal parameters. 
(cf. [Parameter Bindings in Reference Manual](../Dafny/Dafny#sec-parameter-bindings))

## **Error: type mismatch for argument _i_ (function expects _type_, got _type_)**

<!-- TODO - may not be reachable -->
_This error message is not yet documented. Please report any source code that provokes it._

## **Error: sequence construction must use an integer-based expression for the sequence size (got _type_)**

```dafny
const s := seq(true, i=>i)
```

The `seq(10, i=>i)` kind of sequence constructor creates a sequence whose size is the value of the first
argument and whose elements are filled by applying the given function to the appropriate number of 
`nat` values (beginning with 0). Accordingly the first argument must be a `nat` and the second a function
from `nat` to values of the element type of the sequence.

## **Error: sequence-construction initializer expression expected to have type '_type_' (instead got '_type_')_hint_**

<!-- %check-resolve %options --type-system-refresh=false --general-traits=legacy --general-newtypes=false -->
```dafny
const s := seq(10, 20)
```

The `seq(10, i=>i)` kind of sequence constructor creates a sequence whose size is the value of the first
argument and whose elements are filled by applying the given function to the appropriate number of 
`nat` values (beginning with 0). Accordingly the first argument must be a `nat` and the second a function
from `nat` to values of the element type of the sequence.

## **Error: can only form a multiset from a seq or set (got _type_)**

```dafny
const m:= multiset(42)
```

The `multiset` function converts a seq or set to a multiset of the same element type. 
So the argument must be one of those types, and not, say an `int` value.

## **Error: the argument of a fresh expression must denote an object or a set or sequence of objects (instead got _type_)**

```dafny
method m() {
  var i: int;
  assert fresh(i);
}
```

The result of the `fresh` predicate is true if the argument has been allocated since the pre-state of the 
two-state context containing the call. Thus the argument must be of a type that is allocatable,
such as a class type --- but not value types like `bool` or `int` or datatypes. The argument may also be
a set or sequence of such allocatable objects.

## **Error: logical/bitwise negation expects a boolean or bitvector argument (instead got _type_)**

```dafny
const x := !1
```

The logical negation operator (`!`) applies to `bool` and bitvector values, but not to, for example,
`int` values without an explicit conversion. In particular there is no conversion between 0 and false
or 1 and true.

## **Error: size operator expects a collection argument (instead got _type_)**

```dafny
method m(x: array<int>) {
  var y: int := |x|;
}
```

The |...| operator is the _size_ operator and returns the integer that is the size of its argument.
Only finite collections (of type `seq`, `set`, `multiset`, `map`) may be the argument of the
size operator -- not arrays, `iset`, or `imap`.

## **Error: a _what_ definition is not allowed to depend on the set of allocated references**

```dafny
class B {}
const bbb: B
predicate p() { allocated(bbb) }
```

A function is allowed to depend on the heap, as if the heap were an implicit parameter to the function. 
Any such dependence on mutable fields must be declared in the function’s reads clause. 
Dafny enforces that a function’s definition (which includes its body and its requires and reads clauses, 
but not any of its ensures and decreases clauses) adheres to its reads clause.
The purpose of the reads clause is to let you determine when the function’s value may have changed. 
If you invoke F(x) twice on the same parameter x, then you expect to get the same value. 
But since the heap is an implicit parameter of the function, will F(x) still give the same value if the heap is changed between the two invocations? 
The reads clause helps answer this question. Suppose the function’s reads clause denotes a set of objects R. 
Then, as long as the fields of the objects in R are the same for the two invocations of F(x), the two invocations will give the same value.
Part of this rule is also that the function is not allowed to depend on the “allocation set”, that is, the set of objects that are currently allocated. 
This is convenient, because a method is always allowed to enlarge the allocation set. 
As an example, consider a function F(x) with an empty reads clause and a method M() with an empty modifies clause. 
From this, Dafny allows you to prove the assertion in the following code:
<!-- %no-check -->
```dafny
var tmp := F(x);
M();
assert tmp == F(x);
```

The non-dependence on the allocation set is checked syntactically by the resolver and the reads clause is enforced by the verifier.
Although it would be possible to extend Dafny's logic so that functions could depend on the allocation set, this is
at present not implemented.

## **Error: type conversion to an int-based type is allowed only from numeric and bitvector types, char, and ORDINAL (got _type_)**

```dafny
const x: int := true as int
```

Not all pairs of types have implicit or even explicit conversions. But there are conversions
to int types from numeric types, including the ORDINAL type; for any source type, the value of 
the numeric expression must be in the range for the int type (if it is a subset type or a newtype).
Even `char` values have an integer representation (and thus a representation as an `int`) 
corresponding to their unicode value.

## **Error: type conversion to a real-based type is allowed only from numeric and bitvector types, char, and ORDINAL (got _type_)**

<!-- %check-resolve %options --type-system-refresh=false --general-traits=legacy --general-newtypes=false -->
```dafny
const x: real := true as real
```

Not all pairs of types have implicit or even explicit conversions. But there are conversions
to real types from numeric types, including the ORDINAL type; for any source type, the value of 
the numeric expression must be in the range for the real type (if it is a subset type or a newtype).
Even `char` values have an real representation corresponding to their (integer) unicode value.


## **Error: type conversion to a bitvector-based type is allowed only from numeric and bitvector types, char, and ORDINAL (got _type_)**

```dafny
const x: bv1 := true as bv1
```

Not all pairs of types have implicit or even explicit conversions. But there are explicit conversions
to bitvector types from numeric types, including the ORDINAL type; for any source type, the value of 
the numeric expression must be in the range for the bitvector type. Even `char` values have a
bitvector representation corresponding to their (integer) unicode value.

## **Error: type conversion to a char type is allowed only from numeric and bitvector types, char, and ORDINAL (got _type_)**

```dafny
const x: char := true as char
```

Not all pairs of types have implicit or even explicit conversions. But there are explicit conversions
to the char type from numeric types, including the ORDINAL type; for any source type, the value of 
the numeric expression must be in the range for the char type. The numeric values for a given
`char` is its numeric unicode representation, which (for `--unicode-char=true`) is in the range 
0 to 0x10FFFF, inclusive, though there are some sub-ranges that are not valid unicode characters.

## **Error: type conversion to an ORDINAL type is allowed only from numeric and bitvector types, char, and ORDINAL (got _type_)**

```dafny
const x: ORDINAL := true as ORDINAL
```

Not all pairs of types have implicit or even explicit conversions. But there are explicit conversions
to the ORDINAL type from numeric types. Even `char` values have an integer representation and 
ORDINAL value corresponding to their unicode value.

## **Error: type cast to reference type '_type_' must be from an expression of a compatible type (got '_type_')**

```dafny
method m(i: int) {
  var x := i as object;
}
```

The Dafny `as` is a type cast. But Dafny only allows such casts (or checks with `is`) between types that could possibly 
be cast from one to the other. In this case, something that is not a reference type is attempting to be cast
to a type that is a reference type.

## **Error: type cast to type '_type_' must be from an expression of a compatible type (got '_type_')**

```dafny
datatype D = A | B
const c := 0 as D
```

The `as` operator is the type conversion operator. But it is only allowed between an expression and a type if it
is syntactically possible for the value to be converted to the type. Some types, such as datatypes,
have no conversions to or from other types. Type conversions from a value of a datatype to some other type are
always identity functions and are not allowed to be written.

## **Error: type test for type '_type_' must be from an expression assignable to it (got '_type_')**

```dafny
datatype D = A | B
const c := 0 is D
```

The `is` operator is the type test operator. It asks whether the expression on the left is a value of the
type on the right. It might be used to see if a value of a trait type is actually a value of some class
derived from that trait, or whether a `int` value is actually a value of some int-based subtype.
However, the `is` operator is not allowed to be used in cases where the type of the expression on the left
means that the expression could never be a value of the type on the right. For example a
class value could never be converted to a datatype value, so an `is` between a reference expression and
a datatype type is not allowed.

## **Error: first argument to _op_ must be of type bool (instead got _type_)**

<!-- %check-resolve %options --type-system-refresh=false --general-traits=legacy --general-newtypes=false -->
```dafny
const b := true
const i := 4
const c := i || b
```

The logical operators `||`, `&&`, `==>`, `<==`, `<==>` take only `bool` arguments.
Dafny does not have any implicit conversion to or from `bool` values.

## **Error: second argument to _op_ must be of type bool (instead got _type_)**

<!-- %check-resolve %options --type-system-refresh=false --general-traits=legacy --general-newtypes=false -->
```dafny
const b := true
const i := 4
const c := b ==> i
```

The logical operators `||`, `&&`, `==>`, `<==`, `<==>` take only `bool` arguments.
Dafny does not have any implicit conversion to or from `bool` values.

## **Error: range of quantified variable must be of type bool (instead got _type_)**

<!-- %check-resolve %options --type-system-refresh=false --general-traits=legacy --general-newtypes=false -->
```dafny
function f(i: set<int>): set<int> { set k: int <- i |  true || k  }
```

In a quantification using the `<-` syntax, the type of the quantified variable is
determined by its explicit declaration or by the type of the elements of the container
(the right-hand operand). If the quantified variable is used as a `bool` value
when it is not a `bool`, this error message occurs.

## **Error: arguments must have comparable types (got _type_ and _type_)**

<!-- %check-resolve %options --type-system-refresh=false --general-traits=legacy --general-newtypes=false -->
```dafny
datatype D = D()
const z := 0 == D()
```

All types have `==` and `!=` operations between two elements of the same type.
And in cases of subtypes and bit-vector types there may be implicit conversions
that allow members of two different but related types to be compared.
But dissimilar types cannot be compared.

## **Error: arguments to _op_ must have a common supertype (got _type_ and _type_)**

```dafny
predicate m(x: int, s: set<int>)  { s !! x }
```

The `!!` operator takes sets as operands. The complaint here is likely that one of the operands is not a set.

<!-- 2 instances -->

## **Error: arguments must be of a set or multiset type (got _type_)**

```dafny
const z := 1 !! 2
```

The `!!` operator denotes disjointness of sets.
It is only permitted between sets or multisets of the same element type.

## **Error: arguments to rank comparison must be datatypes (got _type_ and _type_)**

```dafny
datatype D = D()
class A {}
method m(a: D, b: A) {
  assert a < b;
  assert a > b;
}
```

The `<` and `>` operators are used for traditional numeric comparison, 
comparison of prefixes in sequences (just `<`),
subset relations among sets,
and for rank (structural depth) comparisons between values of the same datatype.
When used for rank comparison, both operands must be values of the same datatype.

## **Error: arguments to _expr_ must have a common supertype (got _type_ and _type_)**

```dafny
const x: ORDINAL
const y: int
const z := y < x 
const w := y >= x 
```

For binary operators, the two operands must be able to be implicitly converted to the same supertype.
For example, two different int-based subtypes would be converted to int, or two values of different
classes that extend the same trait could be converted to values of that trait.
Where Dafny cannot determine such a common supertype, the comparison is illegal and this error message results.

## **Error: arguments to _op_ must be of a numeric type, bitvector type, ORDINAL, char, a sequence type, or a set-like type (instead got _type_)**

```dafny
const x: map<int,int>
const z := x < x 
```

The `<`, `<=`, `>=`, and `>` operators are used for traditional numeric comparison, 
comparison of prefixes in sequences (just `<`),
and subset relations among sets.
But they are not used for comparing maps or reference values.

<!-- 2 instances -->

## **Error: type of _op_ must be of a bitvector type (instead got _type_)**

```dafny
const z :=  0 << 1
```

The `<<` and `>>` operators are left- and right-shift operations. 
They shift a bit-vector value by a given integer number of bits.
The left-hand operand must be a value of a bit-vector type.
Even int literals are not implicitly converted to bitvectors 
(because Dafny would not know which bit-vector type to use).
An explicit conversion is required.

## **Error: type of left argument to _op_ (_type_) must agree with the result type (_type_)**

<!-- TODO - this is about << and >> operators -- not sure it is reachable -->

## **Error: type of right argument to _op_ (_type_) must be an integer-numeric or bitvector type**

```dafny
const z :=  (1 as bv4) << true
```

The `<<` and `>>` operators are left- and right-shift operations. 
They shift a bit-vector value by a given integer number of bits.
The right-hand operand must be an integer value,
but its type may be an int-based type (such as a subtype) or
a bit-vector type.

## **Error: type of + must be of a numeric type, a bitvector type, ORDINAL, char, a sequence type, or a set-like or map-like type (instead got _type_)**

```dafny
datatype D = D()
const z := D() + D()
```

The `+` operand in Dafny is used for traditional numeric addition, for concatenation of sequences, and for unions.
But not for all types. There is no `+` for datatypes or references, for example.

## **Error: type of left argument to + (_type_) must agree with the result type (_type_)**

<!-- %check-resolve %options --type-system-refresh=false --general-traits=legacy --general-newtypes=false -->
```dafny
const z := 0 + {1}
```

Though the `+` operand applies to many of Dafny's types, the left- and right- operand need to be
the same type or convertible to the same type. For example, there is no conversion from a type to a 
collection of that type.

## **Error: type of right argument to + (_type_) must agree with the result type (_type_)**

```dafny
const z := {1} + 0
```

Though the `+` operand applies to many of Dafny's types, the left- and right- operand need to be
the same type or convertible to the same type. For example, there is no conversion from a type to a 
collection of that type.

## **Error: type of - must be of a numeric type, a bitvector type, ORDINAL, char, or a set-like or map-like type (instead got _type_)**

```dafny
datatype D = D()
const z := D() - D()
```

The `-` operand in Dafny is used for traditional numeric subtraction, for set difference,
and key removal from maps.
But not for all types. There is no `-` for datatypes or references, for example.


## **Error: type of left argument to - (_type_) must agree with the result type (_type_)**

<!-- %check-resolve %options --type-system-refresh=false --general-traits=legacy --general-newtypes=false -->
```dafny
const z := 0 - {1}
```

Though the `-` operand applies the many of Dafny's types, the left- and right- operand need to be
the same type or convertible to the same type. For example, there is no conversion from a type to a 
collection of that type.

## **Error: map subtraction expects right-hand operand to have type _type_ (instead got _type_)**

```dafny
function f(mx: map<int,int>, my: map<int,int>): map<int,int> { mx - my }
```

The map subtraction operator takes a map and a set as operands; 
the set denotes those elements of the map's _domain_ that are removed.

## **Error: type of right argument to - (_type_) must agree with the result type (_type_)**

```dafny
const z := {1} - 0
```

Though the `-` operand applies to many of Dafny's types, the left- and right- operand need to be
the same type or convertible to the same type. For example, there is no conversion from a type to a 
collection of that type.


## **Error: type of * must be of a numeric type, bitvector type, or a set-like type (instead got _type_)**

```dafny
function ff(j: map<int,int>): map<int,int> { j * j }
```

The `*` operator is defined to either multiply numeric vales or take the interesection of sets and multisets.

## **Error: type of left argument to * (_type_) must agree with the result type (_type_)**

<!-- TODO -->

## **Error: type of right argument to * (_type_) must agree with the result type (_type_)**

```dafny
function ff(i: int, j: real): real { j * i }
```

The types of the two arguments of `*` must be the same (or implicitly convertible to be the same).
Typically the result of the expression is determined by the left operand.
This message then is stating that the right operand has a different type.


## **Error: second argument to _op_ must be a set, a multiset, a sequence with elements of type int, or a map with domain int (instead got _type_)**

```dafny
function ff(i: int, j: real): bool { i in j }
```

The operators `in` and `!in` test membership of a value in a container,
so the right-hand operand must be a container of some sort.
It may also be a map, in which case membership in the map's domain is checked, but this use
is deprecated in favor of `i in m.Keys`,

## **Error: domain of quantified variable must be a set, multiset, or sequence with elements of type _type_, or a map with domain _type_ (instead got _type_)**

<!-- %check-resolve %options --type-system-refresh=false --general-traits=legacy --general-newtypes=false -->
```dafny
function f(i: int): set<bool> { set k <- i |  k }
```

The syntax `k <- i` means that `k` is a quantified variable whose domain is all the elements of the container `i`.
So the type of `i` must be a container, such as a set, in which case the type of `k` is the type of elements of the container.
If the right-hand operand is a `map`, then `k` has the type of the domain of the map.

<!-- up to line 840 -->






