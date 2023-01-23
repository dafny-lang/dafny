<!-- %check-resolve %default %useHeadings -->

<!-- DafnyCore/Resolver/ExpressionTester.cs -->

## **Error: ghost variables such as _name_ are allowed only in specification contexts. _name_ was inferred to be ghost based on its declaration or initialization.**

<!-- %check-resolve -->
```dafny
method m() {
  ghost var i := 6;
  var j := i;
  print j;
}
```

By their nature, ghost variables and ghost expressions generally may not affect the
compiled code. So ghost variables may not be used in any non-ghost (compiled) statement.
Note that variables can be ghost because they are explicitly declared to be ghost
or because they are initialized with a value that is derived from a ghost expression.

## **Error: a _what_ is allowed only in specification contexts**

```dafny
datatype A = A(x: int, ghost y: int)
method m(a: A) returns (r: int) {
    return a.y;
}
```

Ghost expressions, including ghost fields or destructors, are allowed only in ghost code.

## **Error: a _what_ with ghost parameters can be used as a value only in specification contexts**

<!-- TODO -->

## **Error: _what_ '_name_' can be used only in specification contexts**

<!-- TODO -->

## **Error: in a compiled context, update of _deconstructors_ cannot be applied to a datatype value of a ghost variant (ghost constructor _constructor_)**

<!-- TODO -->

## **Error: a call to a _kind_ is allowed only in specification contexts**

```dafny
twostate function f(): int { 42 }
method m() returns (r: int) {
  r := f();
}
```

`twostate`, extreme predicates, and prefix lemmas are functions that are always ghost (even without a `ghost` keyword).
Thus they may never be used outside a ghost context.

## **Error: a call to a ghost _what_ is allowed only in specification contexts (consider declaring the _what_ with 'function method')**

For Dafny 3:
<!-- %check-resolve %options --function-syntax:3 -->
```dafny
function f(): int { 42 }
method m() returns (a: int)
{
  a := f();
}
```

## **Error: a call to a ghost _what_ is allowed only in specification contexts (consider declaring the _what_ without the 'ghost' keyword)**
For Dafny 4:
<!-- %check-resolve %options --function-syntax:4 -->
```dafny
ghost function f(): int { 42 }
method m() returns (a: int)
{
  a := f();
}
```

A ghost function can only be called in a ghost context; assigning to an out-parameter is
always a non-ghost context. If you declare the function to be compilable, then it can be used
in a non-ghost context. In Dafny 3 a non-ghost function s declared as `function method` (and just `function` is ghost);
in Dafny 4, `function` is non-ghost and `ghost function` is ghosts (like the declarations
for methods). See [the reference manual on --function-syntax](../DafnyRef/DafnyRef#sec-function-syntax).

## **a call to a ghost {what} is allowed only in specification contexts (consider declaring the {what} with '{what} method')**

<!-- TODO -->

## **Error: ghost constructor is allowed only in specification contexts**

<!-- %check-resolve -->
```dafny
datatype D = A | ghost C
method m(i: int) returns (r: D){
  if i == 0 { r := A; }
  if i != 0 { r := C; }
}
```

A datatype can have a mix of non-ghost and ghost constructors, but the ghost constructors
may only be used in ghost contexts.
For example, a ghost constructor cannot be assigned to a non-ghost out-parameter
or used in the then- or else-branch of a non-ghost if statment.

## **Error: old expressions are allowed only in specification and ghost contexts**

<!-- %check-resolve -->
```dafny
class A {}
method m(a: A) returns (r: A){
  r := old(a);
}
```

The `old` construct is only used in ghost contexts. Typically using `old`
forces an expression to be ghost.
But in situations where it is definitely not a ghost context, such as
assiging to a non-ghost out-parameter or the actual aargument for a
non-ghost formal parameter, then `old` cannot be used.

## **Error: an expression of type '_type_' is not run-time checkable to be a '_type_'**

<!-- TODO -->

## **Error: fresh expressions are allowed only in specification and ghost contexts**

<!-- %check-resolve -->
```dafny
class A {}
method m(a: A) returns (b: bool){
  b := fresh(a);
}
```

The `old` construct is only used in ghost contexts. Typically using `old`
forces an expression to be ghost.
But in situations where it is definitely not a ghost context, such as
assiging to a non-ghost out-parameter or the actual argument for a
non-ghost formal parameter, then `old` cannot be used.

## **Error: unchanged expressions are allowed only in specification and ghost contexts**

<!-- %check-resolve -->
```dafny
class A {}
method m(a: A) returns (b: bool){
  b := unchanged(a);
}
```

The `unchanged` construct is only used in ghost contexts. Typically using `unchanged`
forces an expression to be ghost.
But in situations where it is definitely not a ghost context, such as
assiging to a non-ghost out-parameter or the actual argument for a
non-ghost formal parameter, then `unchanged` cannot be used.

## **Error: rank comparisons are allowed only in specification and ghost contexts**

```dafny
datatype D = A | B
method m(dd: D) 
{
  var d := A;
  print d < dd;
}
```

The `<` operator for two datatype values denotes _rank comparison_. That is,
the right-hand operand must be structurally deeper than the left for the result
of the operator to be true. However, this operation is always a ghost operation 
and is never compiled. So it cannot appear in a non-ghost context.

## **Error: prefix equalities are allowed only in specification and ghost contexts**

<!-- TODO -->

## **Error: _what_ in non-ghost contexts must be compilable, but Dafny's heuristics can't figure out how to produce or compile a bounded set of values for '_name_'**

```dafny
const s := iset i: int :: i*2 
```

Implicit iterations over unbounded ranges are not compilable. 
More typically a _range_ predicate is given that limits the range of the local variable.
The dafny tool analyzes this predicate, using various heuristics, to find lower and
upper bounds by which to constrain the range. If the heuristics fail, then dafny
does not know how to, and will not, compile the code. Where possible, adding in a
range predicate, even if it is a superset of the actual range, can give the compiler
enough hints to construct a compiled version of the program.

## **Error: match expression is not compilable, because it depends on a ghost constructor**

```dafny
datatype D = A | ghost B
method m(dd: D) 
{
  print match dd { case A => 0 case B => 1 };
}
```

If one of the cases in a match expression uses a ghost constructor, then the whole
match expression is ghost. That match expression cannot then be used in a compiled
context, such as a print statement.

<!-- ./DafnyCore/Resolver/NameResolutionAndTypeInference.cs -->

## **Error: newtypes must be based on some numeric type (got _type_)**

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

The expression after the vertical bar is should be a boolean condition.
The values of the basetype that satisfy this condition are the members 
of the newtype. This is different than, say, a set comprehension like
`set i: int :: i*2` where the expression after the `::` gives the elements
of the set directly.

## **Error: subset-type constraint must be of type bool (instead got _type_)**

```dafny
type T = i: int | i
```

The expression after the vertical bar is should be a boolean condition.
The values of the basetype that satisfy this condition are the members 
of the subset type. This is different than, say, a set comprehension like
`set i: int :: i*2` where the expression after the `::` gives the elements
of the set directly.

## **Error: witness expression must have type '_type_' (got '_type_')**

```dafny
type T = i: int | 100 < i < 102 witness true
```

In some definitions of subset types or newtypes, Dafny needs an example value
to know that the type is not empty. That value is called a `witness` and 
is a specific value that can be proved to be a member of the type.
Since it is a member of the newly defined type, and hence of the basetype,
the witness may not be an expression of some different type.

<!-- 2 instances -->

## **Error: type of argument of a unary - must be of a numeric or bitvector type (instead got _type_)**

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

## **Error: type of real literal is used as _type_**

<!-- TODO -->

## **Error: 'this' is not allowed in a 'static' context**

```dafny
class A {}
method m() {
  var a: A := this;
}
```

As in some other programming languages, `this` in Dafny refers to the object that contains 
the method in which this reference to `this` is used. However, the containing object is
an implicit argument to a method only if it is an _instance_ method, not if it is a
_static_ method; so `this` cnanot be used in static methods.

A method in a class is instance by default and static only if it is explicitly
declared so. A method declared at the top-level or as a direct member of a 
module is implicitly static (and cannot be instance). 

## **Error: Identifier does not denote a local variable, parameter, or bound variable: _name_**

<!-- TODO -->

## **Error: Undeclared datatype: _type_**

<!-- TODO -->

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

<!-- TODO -->

## **Error: All elements of display must have some common supertype (got _type_, but needed type or type of previous elements is _type_)**

<!-- TODO -->

<!-- 3 instance -->

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

<!-- TODO - fix - different error message for this example -->
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
where the state are the pre-state of the method and the current state at the
location of the call. However, outside of a method, such as initializations 
of const declarations are not two-state contexts.

## **Error: a field must be selected via an object, not just a class name**

<!-- TODO -->

## **Error: member _name_ in type _type_ does not refer to a field or a function**

<!-- TODO - not sure this is reachable -->

## **Error: array selection requires an array_n_ (got _type_)**

<!-- TODO - fix - different error message for this example -->

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

## **Error: update requires a sequence, map, or multiset (got _type_)**

```dafny
method m(i: int, s: seq<int>) 
  requires |s| > 100
{
  var ss := i[0 := 10];
}
```

The update syntax provides a way to produce a slightly modified sequence, multiset, or map:
if `s` is a `seq<int>`, then `s[0 := 10]` is a `seq<int>` with the same values at the same positions
as `s`, except that the value at position 0 is now 10. It is important to understand that
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
three actual arguments, which must correespond to the formal argument in the definition of `f`.
This syntax is only legal if the expression prior to the left parenthesis is a function,
and not something else. It need not be just an identifier; it could be a expression, such
as a lambda expression: `((f:int)=>42)(1)`.

## **Error: wrong number of arguments to function application (function type '_type_' expects _number_, got _number_)**

<!-- TODO - fix - different error message for this example -->

```dafny
const k := ((f:int)=>42)(1,2);
```

This message indicates that in some kind of function call, the number of actual arguments does
not match the number of formal parameters (as given in the function definition).
Usually the actuals and formals must match exactly, but Dafny does allow
for optional and named arguments with default values. In those cases, the number of actual
arguments may be less than the number of formal parameters. 
(cf. [Parameter Bindings in Reference Manual](../Dafny/Dafny#sec-parameter-bindings))

## **Error: type mismatch for argument _i_ (function expects _type_, got _type_)**

<!-- TODO -->

## **Error: sequence construction must use an integer-based expression for the sequence size (got _type_)**

```dafny
const s := seq(true, i=>i)
```

The `seq(10, i=>i)` kind of sequence constructor creates a sequence whose size is the value of the first
argument and whose elements are filled by applying the given function to the appropriate number of 
`nat` values (beginning with 0). Accordingly the first argument must be a `nat` and the second a function
from `nat` to values of the element type of the sequence.

## **Error: sequence-construction initializer expression expected to have type '_type_' (instead got '_type_')_hint_**

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
two-state context containing thte call. Thus the argument must be of a type that is allocatable,
such as a class type --- but not value types like `bool` or `int` or datatypes. 

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

<!-- TODO -->

## **Error: type conversion to an int-based type is allowed only from numeric and bitvector types, char, and ORDINAL (got _type_)**

```dafny
const x: int := true as int
```

Not all pairs of types have implicit or even explicit conversions. But there are conversions
to int types from numeric types, including the ORDINAL type; for any source type, the value of 
the numeric expression must be in the range for the int type (if it is a subset type or a newtype).
Even `char` values have an integer representation (and thus a represetnation as a `real`) 
corresponding to their unicode value.

## **Error: type conversion to a real-based type is allowed only from numeric and bitvector types, char, and ORDINAL (got _type_)**

```dafny
const x: real := true as real
```

Not all pairs of types have implicit or even explicit conversions. But there are conversions
to real types from numeric types, including the ORDINAL type; for any source type, the value of 
the numeric expression must be in the range for the int type (if it is a subset type or a newtype).
Even `char` values have an integer representation corresponding to their unicode value.


## **Error: type conversion to a bitvector-based type is allowed only from numeric and bitvector types, char, and ORDINAL (got _type_)**

```dafny
const x: bv1 := true as bv1
```

Not all pairs of types have implicit or even explicit conversions. But there are explicit conversions
to bitvector types from numeric types, including the ORDINAL type; for any source type, the value of 
the numeric expression must be in the range for the bitvector type. Even `char` values have an
integer representation corresponding to their unicode value.

## **Error: type conversion to a char type is allowed only from numeric and bitvector types, char, and ORDINAL (got _type_)**

```dafny
const x: char := true as char
```

Not all pairs of types have implicit or even explicit conversions. But there are explicit conversions
to the char type from numeric types, including the ORDINAL type; for any source type, the value of 
the numeric expression must be in the range for the char type. The numeric values for a given
`char` is its numeric unicode representation, which (for `--unicode-char=true`) is the range 
0 to 0x10FFFF, inclusive.

## **Error: type conversion to an ORDINAL type is allowed only from numeric and bitvector types, char, and ORDINAL (got _type_)**

```dafny
const x: ORDINAL := true as ORDINAL
```

Not all pairs of types have implicit or even explicit conversions. But there are explicit conversions
to the ORDINAL type from numeric types. Even `char` values have an integer representation and 
ORDINAL value corresponding to their unicode value.

## **Error: type cast to reference type '_type_' must be from an expression assignable to it (got '_type_')**

```dafny
method m(i: int) {
  var x := i as object;
}
```

The Dafny `as` is a type cast. But Dafny only allows such casts (or checks with `is`) between types that could possibly 
be cast from one to the other. In this case, something that is not a reference type is attempting to be cast
to a type that is a reference type.

## **Error: type conversions are not supported to this type (got _type_)**

```dafny
datatype D = A | B
const c := 0 as D
```

The `as` operator is the type conversion operator. But it is only allowed between an expression and a type if it
is syntactically possible for the value to be converted to the type. Some types, such as datatypes,
have no conversions to or from the type. Type conversions from a value of a datatype to that type are
always identity functions and are not allowed to be written either.

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

```dafny
const b := true
const i := 4
const c := i || b
```

The logical operators `||`, `&&`, `==>`, `<==`, `<==>` take only `bool` arguments.
Dafny does not have any implicit conversion to or from `bool` values.

## **Error: second argument to _op_ must be of type bool (instead got _type_)**

```dafny
const b := true
const i := 4
const c := b ==> i
```

The logical operators `||`, `&&`, `==>`, `<==`, `<==>` take only `bool` arguments.
Dafny does not have any implicit conversion to or from `bool` values.

## **Error: range of quantified variable must be of type bool (instead got _type_)**

<!-- TODO - fix - different error message for this example -->

```dafny
const c := forall i: int | true && i :: true
```

In a quantified expression, the expression between the `|` and the `::` is the 
_range_ expression. It serves to limmit the values of the quantified variable(s)
that are to be considered in evaluating the exp[ression after the `::`. 
As such, this range expression must always have a `bool` type.

## **Error: arguments must have comparable types (got _type_ and _type_)**

```dafny
datatype D = D()
const z := 0 == D()
```

All types have `==` and `!=` operations between two elements of the same type.
And in cases of subtypes and bit-vector types there may be implicit conversions
that allow members of two different but related types to be compared.
But dissimilar types cannot be compared.

## **Error: arguments to _op_ must have a common supertype (got _type_ and _type_)**

<!-- TODO -- left and right operands of !! -->

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
}
```

The `<` and `>` operators are used for traditional numeric comparison, 
comparison of prefixes in sequences (just `<`),
subset relations among sets,
and for rank (structural depth) comparisons between values of the same datatype.
But both operands must be values of the some datatype.

<!--two instances, for < and for > -->

## **Error: arguments to _expr_ must have a common supertype (got _type_ and _type_)**

```dafny
const x: ORDINAL
const y: int
const z := y < x 
```

For binary operators, the two operands must be able to be implicitly converted to the same supertype.
FOr example, two different int-based subtypes would be converted to int, or two values of different
classes that extend the same trait could be converted to values of that trait.
Where Dafny cannot determine such a common supertype, the comparison is illegal and this error message results.

<!--two instances, for < <= and for > >= -->

## **Error: arguments to _op_ must be of a numeric type, bitvector type, ORDINAL, char, a sequence type, or a set-like type (instead got _type_ and _type_)**

```dafny
const x: map<int,int>
const z := x < x 
```

The `<`, `<=`, `>=`, and `>` operators are used for traditional numeric comparison, 
comparison of prefixes in sequences (just `<`),
and subset relations among sets.
But they are not used for comparing maps or reference values.

<!--two instances, for < <= and for > >= -->

## **Error: type of _op_ must be a bitvector type (instead got _type_)**

```dafny
const z :=  0 << 1
```

The `<<` and `>>` operators are left- and right-shift operations. 
They shift a bit-vector value by a given integer number of bits.
The left-hand operand must be a value of a bit-vector type.
Even int literals are not implicitly converted to bitvectors 
(because Dafny wuld not know which bit-vector type to use).
An explicit conversion is required.

## **Error: type of left argument to _op_ (_type_) must agree with the result type (_type_)**

<!-- TODO - this is about << and >> operators -->

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

```dafny
const z := 0 + {1}
```

Though the `+` operand applies the many of Dafny's types, the left- and right- operand need to be
the same type or convertible to the same type. For example, there is no conversion from  a type to a 
collection of that type.

## **Error: type of right argument to + (_type_) must agree with the result type (_type_)**

```dafny
const z := {1} + 0
```

Though the `+` operand applies the many of Dafny's types, the left- and right- operand need to be
the same type or convertible to the same type. For example, there is no conversion from  a type to a 
collection of that type.

## **Error: type of - must be of a numeric type, bitvector type, ORDINAL, char, or a set-like or map-like type (instead got _type_)**

```dafny
datatype D = D()
const z := D() - D()
```

The `-` operand in Dafny is used for traditional numeric subtraction, and for set difference,
and key removal from maps.
But not for all types. There is no `-` for datatypes or references, for example.


## **Error: type of left argument to - (_type_) must agree with the result type (_type_)**

```dafny
const z := 0 - {1}
```

Though the `-` operand applies the many of Dafny's types, the left- and right- operand need to be
the same type or convertible to the same type. For example, there is no conversion from  a type to a 
collection of that type.

## **Error: map subtraction expects right-hand operand to have type _type_ (instead got _type_)**

<!-- TODO -->

## **Error: type of right argument to - (_type_) must agree with the result type (_type_)**

```dafny
const z := {1} - 0
```

Though the `-` operand applies the many of Dafny's types, the left- and right- operand need to be
the same type or convertible to the same type. For example, there is no conversion from  a type to a 
collection of that type.


## **Error: type of * must be of a numeric type, bitvector type, or a set-like type (instead got _type_)**

<!-- TODO -->

## **Error: type of left argument to * (_type_) must agree with the result type (_type_)**

<!-- TODO -->

## **Error: type of right argument to * (_type_) must agree with the result type (_type_)**

<!-- up to line 840 -->











<!-- ./DafnyCore/Resolver/TypeInferenceChecker.cs -->

## **Error: newtype's base type is not fully determined; add an explicit type for '_name_'**

<!-- TODO -->

## **Error: subset type's base type is not fully determined; add an explicit type for '_name_'**

<!-- TODO -->

## **Error: shared destructors must have the same type, but '_name_' has type '_type_' in constructor '_name_' and type '_type_' in constructor '_name_'**

<!-- TODO -->

## **Error: literal (_literal_) is too large for the bitvector type _type_**

```dafny
const b: bv4 := 30
```

An integer literal can be converted implicitly to a value of a bitvecotr type,
but only if the integer literal is in the range for the target type.
For example, the type `bv4` has 4 bits and holds the values 0 through 15.
So a `bv4` can be initialized with a value in that range.
Negative values are allowed: a value of -n corresponds to the bit vector
value which, when added to the bitvector value of n, gives 0.
For bv4, -n is the same as 16-n.

## **Error: unary minus (-{0}, type {1}) not allowed in case pattern**

<!-- TODO -->

## **Error: type of type parameter could not be determined; please specify the type explicitly**

<!-- TODO -->

## **Error: type of bound variable '{bv.Name}' could not be determined; please specify the type explicitly**

<!-- TODO -->

## **Error: type of bound variable '_name_' ('_type_') is not allowed to use type ORDINAL**

<!-- TODO -->

## **Warning: the quantifier has the form 'exists x :: A ==> B', which most often is a typo for 'exists x :: A && B'; if you think otherwise, rewrite as 'exists x :: (A ==> B)' or 'exists x :: !A || B' to suppress this warning**

<!-- TODO -->

## **Error: type parameter '_name_' (inferred to be '_type_') to the _kind_ '_name_' could not be determined**

<!-- TODO -->

## **Error: type parameter '_name_' (passed in as '_type_') to the _kind_ '_name_' is not allowed to use ORDINAL**

<!-- TODO -->

## **Error: type parameter '_name_' (inferred to be '_type_') in the function call to '_name_' could not be determined**

<!-- TODO -->

## **Error: type parameter '_name_' (inferred to be '_type_') in the function call to '_name_' could not be determined. If you are making an opaque function, make sure that the function can be called.**

<!-- TODO -->

## **Error: type parameter '_name_' (passed in as '_type_') to function call '_name_' is not allowed to use ORDINAL**

<!-- TODO -->

## **Error: the type of the bound variable '_var_' could not be determined**

<!-- TODO -->

## **Error: a type cast to a reference type (_type_) must be from a compatible type (got _type_); this cast could never succeed**

<!-- TODO -->

## **a type test to '_type_' must be from a compatible type (got '_type_')**

<!-- TODO -->

## **a non-trivial type test is allowed only for reference types (tried to test if '_type_' is a '_type_')**

<!-- TODO -->

## **Warning: the type of the other operand is a non-null type, so this comparison with 'null' will always return '_bool_'**

<!-- %check-resolve-warn -->
```dafny
class C {}
function f(): C
method m(c: C) {
  var b: bool := f() != null;
}
```

Dafny does have a `null` value and expressions of types that include `null` can have a `null` value.
But in Dafny, for each class type `C` there is a corresponding type `C?`; `C` does not include `null`,
whereas `C?` does. So if an expression `e` having type `C` is comared against `null`, as in `e == null`,
that comparison will always be `false`. If the logic of the program allows `e` to be sometimes `null`,
then it should be declared with a type like `C?`.

## **Warning: the type of the other operand is a non-null type, so this comparison with 'null' will always return '_bool_' (to make it possible for _name_ to have the value 'null', declare its type to be '_type_')**

<!-- %check-resolve-warn -->
```dafny
class C {}
method m(c: C) {
  var b: bool := c != null;
}
```

Dafny does have a `null` value and variables of types that include `null` can have a `null` value.
But in Dafny, for each class type `C` there is a corresponding type `C?`; `C` does not include `null`,
whereas `C?` does. So if a variable `v` declared as type `C` is comared against `null`, as in `v == null`,
that comparison will always be `false`. If the logic of the program allows `v` to be sometimes `null`,
then it should be declared with a type like `C?`.


## **Warning: the type of the other operand is a _what_ of non-null elements, so the _non_inclusion test of 'null' will always return '_bool_'**

<!-- %check-resolve-warn -->
```dafny
class C {}
method m(c: seq<C>, cc: seq<C?>) {
  var bb := null in cc;  // OK
  var b  := null in c;   // Warning
}
```

This error refers to the `in` (or `!in`) operation and notes that the test is whether `null` is in the given container.
But the elements of the container are of a type that does not include `null`, so the given test will always
be `false` (or `true`).  Either the type of the container's elements should be a nullable type (a `C?` instead of a `C`)
or the test is unnecessary. 

## **Warning: the type of the other operand is a map to a non-null type, so the inclusion test of 'null' will always return '_bool_'**

<!-- TODO -->

## **the type of this _var_ is underspecified**

<!-- TODO -->

## **Error: an ORDINAL type is not allowed to be used as a type argument**

<!-- %no-check This example does not work TODO -->
```dafny
type X<T>
method m(c: X<ORDINAL>) {
}
```

The ORDINAL type corresponds to a mathematical type "larger" than the natural numbers. That is, there
are ORDINALs that are larger than any `nat`. Logical reasoning with ORDINALs is tricky and
a bit counter-intuitive at times. For logical implementation reasons, Dafny limits where
ORDINALs can be used; one restriction is that the ORDINAL type may not be a type argument.

<!-- ./DafnyCore/Resolver/Abstemious.cs-->

## **the value returned by an abstemious function must come from invoking a co-constructor**

<!-- TODO -->

## **an abstemious function is allowed to invoke a codatatype destructor only on its parameters**

<!-- TODO -->

## **an abstemious function is allowed to codatatype-match only on its parameters**

<!-- TODO -->

## **an abstemious function is allowed to codatatype-match only on its parameters**

<!-- TODO -->

## **an abstemious function is not only allowed to check codatatype equality**

<!-- TODO -->

<!-- TODO: Oddly worded message -->


<!-- ./DafnyCore/Resolver/GhostInterestVisitor.cs-->

## **Error: expect statement is not allowed in this context (because this is a ghost method or because the statement is guarded by a specification-only expression)**

<!-- %check-resolve -->
```dafny
method m(ghost b: bool)
{
  var x := 0;
  if b { expect x == 0; }
}
```

`expect` statements are not allowed in ghost contexts; use an `assert` setatement instead.
Ghost context can be explicitly clear, such as the body of a method or function declared `ghost`.
But a ghost context can also be implicit, and not so obvious: if part of a statement,
such as the condition of an if statement or loop or the expression being matched in a match 
statement, is ghost the rest of the statement may be required to be ghost.

## **Error: print statement is not allowed in this context (because this is a ghost method or because the statement is guarded by a specification-only expression)**

<!-- %check-resolve -->
```dafny
method m(ghost b: bool)
{
  if b { print true; }
}
```

`print` statements are not allowed in ghost contexts, because they have external effects.
Ghost context can be explicitly clear, such as the body of a method or function declared `ghost`.
But a ghost context can also be implicit, and not so obvious: if something ghost is part of a statement,
such as the condition of an `if` statement or loop or the expression being matched in a match 
statement, then the rest of the statement may be required to be ghost.

## **ghost-context _kind_ statement is not allowed to _kind_ out of non-ghost _target_**

<!-- TODO -->

## **_kind_ statement is not allowed in this context (because it is guarded by a specification-only expression)**

<!-- TODO -->

## **cannot assign to _var_ in a ghost context**

<!-- TODO -->

## **_var_ cannot be assigned a value that depends on a ghost**

<!-- TODO -->

## **in _proof_, calls are allowed only to lemmas**

<!-- TODO -->

## **only ghost methods can be called from this context**

<!-- TODO -->

## **actual out-parameter _parameter_ is required to be a ghost variable**

<!-- TODO -->

## **actual out-parameter _parameter_ is required to be a ghost field**

<!-- TODO -->

## **actual out-parameter _parameter_ is required to be a ghost variable**

<!-- TODO array update -->

## **a loop in _context_ is not allowed to use 'modifies' clauses**

<!-- TODO -->

## **Error: 'decreases *' is not allowed on ghost loops**

<!-- %check-resolve -->
```dafny
method m()
  decreases *
{
  ghost var c := 10;
  while 0 <= c 
    invariant 0 <= c <= 10;
    decreases *
  {
    c := c - 1;
  }
}
```

A while loop is ghost if its controlling condition is a ghost expression.
Simiarly, a for loop is ghost if the range over which the index variable ranges is ghost.
Ghost code is meant to aid proofs; for sound proofs any constructs in the ghost code must be terminating.
Hence, indications of non-terminating loops, that is, `decreases *`, are not permitted.

This does mean that specifier has to do the work of designing a valid terminating condition and proving it.

<!-- 2 instances -->

## **Error: a loop in _proof_ is not allowed to use 'modifies' clauses**

```dafny
class A {  }
lemma m(j: int, a: A) {
  var i := j;
  while (i > 0) 
    modifies a
  {
  }
}
```

A proof context, such as the body of a lemma, is ghost context and thus is not allowed to modify
anything on the heap. If there is nothing that may be modified, then there is no need for
a `modifies` clause for a loop. Note that the `modifies` clause does not list any local 
variables that are changed in a loop in any case.

## **Error: a ghost loop must be terminating; make the end-expression specific or add a 'decreases' clause**

<!-- TODO -->

## **Error: _proof_ is not allowed to perform an aggregate heap update**

<!-- TODO -->

## **Error: forall statements in non-ghost contexts must be compilable, but Dafny's heuristics can't figure out how to produce or compile a bounded set of values for '{0}'**

<!-- TODO -->

## **Error: a modify statement is not allowed in _proof_**

```dafny
class A {  }
lemma m(a: A)
 {
  modify a;
}
```

A proof context, such as the body of a lemma or a `by` block, is ghost context and thus is 
not allowed to modify anything on the heap. If there is nothing that may be modified, 
then there is no need for a `modify` statement in such a context.

## **Error: _proof_ is not allowed to use 'new'**

```dafny
class A {  }
lemma m(a: A)
{
  var aa := new A;
}
```

A proof context, such as the body of a lemma or a `by` block, is ghost context and thus is 
not allowed to modify anything on the heap. That includes allocating new things in the 
heap, as a `new` expression does. Typically a proof uses expressions that are value types
(sequences, sets, maps) to formulate the proof and not heap operations.

## **Error: _proof_ is not allowed to make heap updates**

<!-- TODO -->

## **Error: assignment to _kind_ is not allowed in this context, because this is a ghost _thing_**

<!-- TODO -->

## **Error: assignment to _kind_ is not allowed in this context, because the statement is in a ghost context; e.g., it may be guarded by a specification-only expression**

<!-- TODO -->

## **Error: the result of a ghost constructor can only be assigned to a ghost variable**

```dafny
class A { constructor I() {} ghost constructor Init(i: int) {} }
method m() returns (a: A)
{
  a := new A.Init(23);
}
```

Classes may have ghost constructors along with regular, non-ghost constructors.
However, ghost constructors may only be called in ghost context, including that
the newly allocated object be assigned to a ghost location (such as a ghost variable). 


<!-- ./DafnyCore/Resolver/TypeConstraint.cs-->

<!-- TODO: collector for other errors? -->

<!-- ./DafnyCore/Resolver/TailRecursion.cs -->

<!-- TODO -->

<!-- ./DafnyCore/Resolver/Resolver.cs -->

<!-- TODO Lots -->

