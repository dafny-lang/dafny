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

```dafny
function f(i: int): int
method m() {
   print f(1);
}
```

Dafny has a fundamental distinction between _ghost_ code and _compiled_ code. Ghost code is not compiled; 
compiled code cannot contain ghost-only features. A function that is explicitly ghost is not permitted in
a context that is compiled, such as a print statement. The distinction can seem a bit blurry because Dafny 
in part infers what is ghost code because of the presence of some ghost features -- so ghost code may not 
be explictly so. Also remember that the declarations of functions in Dafny 4 is 'ghost function' for
ghost and 'function' for non-ghost; in Dafny 3 the declarations are 'function' for ghost, 
and 'function method' for non-ghost.

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

```dafny
codatatype Stream = SNil | SCons(head: int, tail: Stream)
const s: Stream
const t: Stream
const b := s == #[1] t
```

The `==#[k]` syntax is [_prefix equality_](../DafnyRef/DafnyRef#sec-co-equality) on two values of the same codatatype.
It means that the two values have the same prefix of k values.
Such operations are not compilable and only allowed in ghost contexts.

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





<!-- ./DafnyCore/Resolver/TypeInferenceChecker.cs -->

## **Error: newtype's base type is not fully determined; add an explicit type for '_name_'**

<!-- TODO -->

## **Error: subset type's base type is not fully determined; add an explicit type for '_name_'**

<!-- TODO -->

## **Error: shared destructors must have the same type, but '_name_' has type '_type_' in constructor '_name_' and type '_type_' in constructor '_name_'**

```dafny
datatype D = A(x: int) | B (x: bool)
```

In defining a datatype, two constructors can both refer to a common destructor, but if they 
do, the two instances must be declared with the same type. To correct this, either
(a) the writer intends there to be two different destructor values, but accidentally
used the same name, in which case change the name of one of them, or (b) they are
intended to be the same, in which case a common type must be chosen.

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

```dafny
const d: bv4
const c := match d { case -0 => 0 case _ => 1 }
```

In a case value of a match expression with a bitvector type, the literals in the cases
may not be negative literals, even though those may be used as bitvector literals in
some other places in Dafny.

<!-- NOTE: This message is also present in Expressions/LitPattern.cs; I believe the message
here in TypeInferenceChecker is never reachable. -->

## **Error: type of type parameter could not be determined; please specify the type explicitly**

<!-- TODO -->

## **Error: type of bound variable '_name_' could not be determined; please specify the type explicitly**

<!-- TODO -->

## **Error: type of bound variable '_name_' ('_type_') is not allowed to use type ORDINAL**

<!-- TODO -->

## **Warning: the quantifier has the form 'exists x :: A ==> B', which most often is a typo for 'exists x :: A && B'; if you think otherwise, rewrite as 'exists x :: (A ==> B)' or 'exists x :: !A || B' to suppress this warning**

<!-- %check-resolve-warn -->
```dafny
ghost const c := exists i: int :: true ==> true
```

The implication `A ==> B` is true if `A` is false or `B` is true. In a `forall` statement one might write,
for example, `0 <= i < 10 ==> a[i] == 0`, claiming that the array element is 0 for the first 10 array elements.
But if one wrote `exists i :: 0 <= i < 10 ==> a[i] == 0` then a value of 10 for `i` satisfies the predicate.
More often one means `exists i :: 0 <= i < 10 && a[i] == 0`, that is, is there an `i` between 0 and 10 for
which the array element is 0. This is such a common mistake that this warning warns about it and asks for
a syntax that explicitly states that the writer means it.

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

```dafny
trait T {}
const m: map<T,T>
const c := null in m
```

The operation is testing whether `null` is a member of the domain of the map value given as the right-hand operand.
But the domain of that map type (the first type parameter) is a non-null type. So this test will trivially always
fail (for `in`) or succeed (for `!in`). If it is actually the case that the map's domain is allowed to contain `null`
then the domain type should be a nullable type like `T?`. If it is not the case that null could be in the domain,
then this test is not needed at all.

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

```dafny
method m(i: int) {
  ghost var b: bool := true;
  label x: while i > 0 {
    while (b) {
      break x;
    }
  }
}
```

A `break` or `continue` statement might be in a ghost loop or block, for example, because the
condition of the loop is ghost. It then may direct the flow of control to break out of some outer enclosing 
loop or block or continue an iteration in an enclosing loop. If that enclosing loop or block is
non-ghost, we have the situation of ghost code affecting the flow of control of non-ghost code.
Consequently a ghost break or continue statement must have as its target some enclosing ghost
block or loop. 

## **_kind_ statement is not allowed in this context (because it is guarded by a specification-only expression)**

```dafny
method m() {
  ghost var b: bool := true;
  if b { return; }
}
```

If the condition of a `if` or `match` statement is a ghost expression, then the whole statement is
considered ghost. And then the stastement can contain no substatements that are forbidden to be ghost.
`return` and `yield` stastements are never ghost, so they cannot appear in a statement whose guarding
value is ghost.

## **cannot assign to _var_ in a ghost context**

<!-- TODO -->

## **_var_ cannot be assigned a value that depends on a ghost**

<!-- TODO -->

## **in _proof_, calls are allowed only to lemmas**

```dafny
method n() {}
method m(aa: A)
{  
  var i: int;
  assert true by {
    n();
  }
}
```

Proof contexts are blocks of statements that are used to contrcut a proof.
Examples are the bodies of lemma, the by-blocks of assert-by statements
and calc statements. A proof context is a ghost context.
In ghost context, no methods may be called, even ghost methods.
Only lemmas may be called.



## **only ghost methods can be called from this context**

```dafny
method n() {}
ghost method m()
{ 
  n();
}
```

The body of a ghost method is a ghost context. So if there are any
method calls in that body, they must be ghost.
Lemmas and ghost functions may also be called.

## **actual out-parameter _parameter_ is required to be a ghost variable**

```dafny
method n() returns (r: int, ghost s: int) {}
method m() returns (r: bool)
{ 
  var x: int;
  var y: int;
  x, y := n();
}
```

The method being called returns a ghost value as one of its out-parameters.
The variable receiving that value is required to be ghost as well.
Note that out-parameters are numbered beginning with 0.

This message can also arise when the receiving left-hand-side expression
is an array element (e.g. a[0]). This is not permitted at all because
arrays are never ghost.

<!-- 2 instances -->

## **actual out-parameter _parameter_ is required to be a ghost field**

```dafny
class A { var a: int }
method n() returns (r: int, ghost s: int) {}
method m(a: array<int>) returns (r: bool)
{ 
  var x: int;
  var y: int;
  x, a[0] := n();
}
```

The method being called returns a ghost value as one of its out-parameters.
The left-hand-side expression receiving that value is required to be ghost as well.
In this case, the lHS expression is a field of an object;
the field itself must be ghost, not simply the whole object.
Note that out-parameters are numbered beginning with 0.


## **a loop in _context_ is not allowed to use 'modifies' clauses**

```dafny
class A { var a: int }
method m(aa: A)
  modifies aa
{ 
  assert true by {
    var i:= 10;
    while (i > 0) 
      decreases i
      modifies aa
    {
    i := i - 1;
    }
  }
}
```

Proof contexts are blocks of statements that are used to contrcut a proof.
Examples are the bodies of lemma, the by-blocks of assert-by statements
and calc statements. A proof context is a ghost context. One of the rules
for ghost contexts is that nothing on the heap may be modified in ghost context.
Consequently there is no need for a modifies clause for loops that might
be used to support the proof in the `by` block.

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

## **Error: forall statements in non-ghost contexts must be compilable, but Dafny's heuristics can't figure out how to produce or compile a bounded set of values for '_name_'**

<!-- TODO ; this might be shadowed by a similar message in ExpressionTester -->

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

```dafny
class A { var a: int }
lemma m(aa: A) {
  aa.a := 1;
}
```

This message can occur in many program situations: the fault is an assignment to a field in the heap
that is not permitted because the assignment statement occurs in a ghost context such as the body
of a lemma or ghost function.

## **Error: assignment to _kind_ is not allowed in this context, because the statement is in a ghost context; e.g., it may be guarded by a specification-only expression**

```dafny
class A { var a: int }
method m(aa: A) {
  ghost var b := true;
  if b { aa.a := 1; }
}
```

This message can occur in many program situations: the fault is an assignment to a field in the heap
that is not permitted because the assignment statement occurs in a ghost context within a generally
non-ghost environment. A coomon example is the the or else branch of a `if` statement that is
deemed a ghost context because the controlling condition for the loop is a ghost expression.
Similar situations arise for loops and match statements.


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

