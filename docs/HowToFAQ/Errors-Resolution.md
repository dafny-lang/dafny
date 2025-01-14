
<!-- %check-resolve %default %useHeadings %check-ids -->

<!-- FILE DafnyCore/Resolver/ExpressionTester.cs -->

## **Error: ghost variables such as _name_ are allowed only in specification contexts. _name_ was inferred to be ghost based on its declaration or initialization.** {#r_ghost_var_only_in_specifications}

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

## **Error: a _what_ is allowed only in specification contexts** {#r_only_in_specification}

```dafny
datatype A = A(x: int, ghost y: int)
method m(a: A) returns (r: int) {
    return a.y;
}
```

Ghost expressions, including ghost fields or destructors, are allowed only in ghost code.

## **Error: a _what_ with ghost parameters can be used as a value only in specification contexts** {#r_ghost_parameters_only_in_specification}

```dafny
class A { 
  function f(ghost i: int): int {0}
}
method m(a:A) 
{
  print a.f;
}
```

Functions may have some (or all) formal parameters be ghost. Such parameters can only be used in ghost expressions
within the function body. There are limits though on where such a function may be used.
For example, passing the value of the function itself (not a call of the function) is restricted to ghost contexts.

## **Error: _what_ '_name_' can be used only in specification contexts** {#r_used_only_in_specification}

```dafny
datatype D = J | ghost K(i: int)
method m(d:D) 
  requires d.K?
{
  print d.i;
}
```

A datatype may have ghost constructors, but accessing the value of one of the fields (destructors) of such a ghost constructor is
a ghost operation. Consequently an expression like `d.i` (where `i` is a destructor of a ghost constructor for the datatype of which `d` is a value)
is allowed only in ghost contexts.

## **Error: in a compiled context, update of _deconstructors_ cannot be applied to a datatype value of a ghost variant (ghost constructor _constructor_)** {#r_ghost_destructor_update_not_compilable}

```dafny
datatype D = A | ghost B(c: int)
method m(d:D) 
  requires d.B?
{
  print d.(c := 0);
}
```

Datatypes may have ghost variants (where the datatype constructor is itself declared ghost), but constructing or updating such variants is a ghost operation.
Consequently such expressions may not be present in compiled code.

## **Error: a call to a _kind_ is allowed only in specification contexts_hint_** {#r_ghost_call_only_in_specification}

```dafny
twostate function f(): int { 42 }
method m() returns (r: int) {
  r := f();
}
```

`twostate` declarations, extreme predicates, and prefix lemmas are always ghost (even without a `ghost` keyword).
Thus they may never be used outside a ghost context.

## **Error: a call to a ghost _what_ is allowed only in specification contexts (consider declaring the _what_ without the 'ghost' keyword)** {#r_ghost_call_only_in_specification_function_4}
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
in a non-ghost context. In Dafny 3 a non-ghost function is declared as `function method` (and just `function` is ghost);
in Dafny 4, `function` is non-ghost and `ghost function` is ghost (like the declarations
for methods). See [the reference manual on --function-syntax](../DafnyRef/DafnyRef#sec-function-syntax).

## **Error: a call to a ghost _what_ is allowed only in specification contexts (consider declaring the _what_ with 'function method')** {#r_ghost_call_only_in_specification_function_3}

For Dafny 3:
<!-- %check-resolve %options --function-syntax:3 -->
```dafny
function f(): int { 42 }
method m() returns (a: int)
{
  a := f();
}
```

A ghost function can only be called in a ghost context; assigning to an out-parameter is
always a non-ghost context. If you declare the function to be compilable, then it can be used
in a non-ghost context. In Dafny 3 a non-ghost function is declared as `function method` (and just `function` is ghost);
in Dafny 4, `function` is non-ghost and `ghost function` is ghost (like the declarations
for methods). See [the reference manual on --function-syntax](../DafnyRef/DafnyRef#sec-function-syntax).

## **Error: ghost constructor is allowed only in specification contexts** {#r_ghost_constructors_only_in_ghost_context}

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

## **Error: old expressions are allowed only in specification and ghost contexts** {#r_old_expressions_only_in_ghost_context}

```dafny
class A {}
method m(a: A) returns (r: A){
  r := old(a);
}
```

The `old` construct is only used in ghost contexts. Typically using `old`
forces an expression to be ghost.
But in situations where it is definitely not a ghost context, such as
assigning to a non-ghost out-parameter or the actual argument for a
non-ghost formal parameter, then `old` cannot be used.

## **Error: an expression of type '_type_' is not run-time checkable to be a '_type_'** {#r_type_test_not_runtime_checkable}

<!-- TODO -->

## **Error: fresh expressions are allowed only in specification and ghost contexts** {#r_fresh_expressions_only_in_ghost_context}

```dafny
class A {}
method m(a: A) returns (b: bool) {
  b := fresh(a);
}
```

The `fresh` construct is only used in ghost contexts. Typically using `fresh`
forces an expression to be ghost.
So `fresh` cannot be used in situations where it is definitely not a ghost context, such as
assigning to a non-ghost out-parameter or the actual argument for a
non-ghost formal parameter.

## **Error: unchanged expressions are allowed only in specification and ghost contexts** {#r_unchanged_expressions_only_in_ghost_context}

```dafny
class A {}
method m(a: A) returns (b: bool){
  b := unchanged(a);
}
```

The `unchanged` construct is only used in ghost contexts. Typically using `unchanged`
forces an expression to be ghost.
So `unchanged` cannot be used in situations where it is definitely not a ghost context, such as
assigning to a non-ghost out-parameter or the actual argument for a
non-ghost formal parameter.

## **Error: rank comparisons are allowed only in specification and ghost contexts** {#r_rank_expressions_only_in_ghost_context}

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

## **Error: prefix equalities are allowed only in specification and ghost contexts** {#r_prefix_equalities_only_in_ghost_context}

```dafny
codatatype Stream = SNil | SCons(head: int, tail: Stream)
const s: Stream
const t: Stream
const b := s == #[1] t
```

The `==#[k]` syntax is [_prefix equality_](../DafnyRef/DafnyRef#sec-co-equality) on two values of the same codatatype.
It means that the two values have the same prefix of k values.
Such operations are not compilable and only allowed in ghost contexts.

## **Error: _what_ in non-ghost contexts must be compilable, but Dafny's heuristics can't figure out how to produce or compile a bounded set of values for '_name_'** {#r_unknown_bounds}

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

## **Error: match expression is not compilable, because it depends on a ghost constructor** {#r_match_not_compilable}

<!-- TODO - does not fail -->
<!-- %no-check -->
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


<!-- FILE ./DafnyCore/Resolver/TypeInferenceChecker.cs -->

## **Error: newtype's base type is not fully determined; add an explicit type for '_name_'** {#r_newtype_base_undetermined}

<!-- TODO -->

## **Error: subset type's base type is not fully determined; add an explicit type for '_name_'** {#r_subset_type_base_undetermined}

<!-- TODO -->

## **Error: shared destructors must have the same type, but '_name_' has type '_type_' in constructor '_name_' and type '_type_' in constructor '_name_'** {#r_shared_destructors_have_different_types}

```dafny
datatype D = A(x: int) | B(x: bool)
```

In defining a datatype, two constructors can both refer to a common destructor, but if they 
do, the two instances must be declared with the same type. To correct this, either
(a) the writer intends there to be two different destructor values, but accidentally
used the same name, in which case change the name of one of them, or (b) they are
intended to be the same, in which case a common type must be chosen.

## **Error: literal (_literal_) is too large for the bitvector type _type_** {#r_literal_too_large_for_bitvector}

```dafny
const b: bv4 := 30
```

An integer literal can be converted implicitly to a value of a bitvector type,
but only if the integer literal is in the range for the target type.
For example, the type `bv4` has 4 bits and holds the values 0 through 15 inclusive.
So a `bv4` can be initialized with a value in that range.
Negative values are allowed: a value of -n corresponds to the bit vector
value which, when added to the bitvector value of n, gives 0.
For bv4, -n is the same as 16-n.

## **Error: unary minus (-_num_, type _type_) not allowed in case pattern** {#r_no_unary_minus_in_case_patterns}

```dafny
const d: bv4
const c := match d { case -0 => 0 case _ => 1 }
```

In a case value of a match expression with a bitvector type, the literals in the cases
may not be negative literals, even though those may be used as bitvector literals in
some other places in Dafny.

<!-- NOTE: This message is also present in Expressions/LitPattern.cs; I believe the message
here in TypeInferenceChecker is never reachable. -->

## **Error: type of type parameter could not be determined; please specify the type explicitly** {#r_type_parameter_undetermined}

<!-- TODO -->

## **Error: type of bound variable '_name_' could not be determined; please specify the type explicitly** {#r_bound_variable_undetermined}

<!-- TODO -->

## **Error: type of bound variable '_name_' ('_type_') is not allowed to use type ORDINAL** {#r_bound_variable_may_not_be_ORDINAL}

<!-- TODO -->

## **Warning: the quantifier has the form 'exists x :: A ==> B', which most often is a typo for 'exists x :: A && B'; if you think otherwise, rewrite as 'exists x :: (A ==> B)' or 'exists x :: !A || B' to suppress this warning** {#r_exists_quantifier_warning}

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

## **Error: type parameter '_name_' (inferred to be '_type_') to the _kind_ '_name_' could not be determined** {#r_type_parameter_not_determined}

<!-- TODO -->

## **Error: type parameter '_name_' (passed in as '_type_') to the _kind_ '_name_' is not allowed to use ORDINAL** {#r_type_parameter_may_not_be_ORDINAL}

<!-- TODO -->

## **Error: type parameter '_name_' (inferred to be '_type_') in the function call to '_name_' could not be determined** {#r_function_type_parameter_undetermined}

<!-- TODO -->

## **Error: type parameter '_name_' (passed in as '_type_') to function call '_name_' is not allowed to use ORDINAL** {#r_function_type_parameter_may_not_be_ORDINAL}

<!-- TODO -->

## **Error: the type of the bound variable '_var_' could not be determined** {#r_bound_variable_type_undetermined}

<!-- TODO -->

## **Error: a type cast to a reference type (_type_) must be from a compatible type (got _type_); this cast could never succeed** {#r_never_succeeding_type_cast}

<!-- TODO -->

## **Error: a type test to '_type_' must be from a compatible type (got '_type_')** {#r_never_succeeding_type_test}

<!-- TODO -->

## **Error: a non-trivial type test is allowed only for reference types (tried to test if '_type_' is a '_type_')** {#r_unsupported_type_test}

<!-- %check-resolve %options --type-system-refresh=false --general-traits=legacy --general-newtypes=false -->
```dafny
type Small = i: nat | i < 10
const i := 10
const b := i is Small
```

The `is` type test is currently somewhat limited in Dafny, and more limited than the companion `as` conversion.
In particular, `is` is not allowed to test that a value is a member of a subset type.

## **Warning: the type of the other operand is a non-null type, so this comparison with 'null' will always return '_bool_'_hint_** {#r_trivial_null_test}

<!-- %check-resolve-warn -->
```dafny
class C {}
function f(): C
method m(c: C) {
  var b: bool := f() != null;
  var a: bool := c != null;
}
```

Dafny does have a `null` value and expressions of types that include `null` can have a `null` value.
But in Dafny, for each class type `C` there is a corresponding type `C?`; `C` does not include `null`,
whereas `C?` does. So if an expression `e` having type `C` is compared against `null`, as in `e == null`,
that comparison will always be `false`. If the logic of the program allows `e` to be sometimes `null`,
then it should be declared with a type like `C?`.

## **Warning: the type of the other operand is a _what_ of non-null elements, so the _non_inclusion test of 'null' will always return '_bool_'** {#r_trivial_null_inclusion_test}

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

## **Warning: the type of the other operand is a map to a non-null type, so the inclusion test of 'null' will always return '_bool_'** {#r_trivial_map_null_inclusion_test}

<!-- %check-resolve-warn %options --type-system-refresh=false --general-traits=legacy --general-newtypes=false -->
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

## **Error: the type of this _var_ is underspecified** {#r_var_type_undetermined}

<!-- TODO -->

## **Error: an ORDINAL type is not allowed to be used as a type argument** {#r_no_ORDINAL_as_type_parameter}
<!-- TODO _ this one is misplaced -->
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

<!-- FILE ./DafnyCore/Resolver/Abstemious.cs -->

## **Error: the value returned by an abstemious function must come from invoking a co-constructor** {#r_abstemious_needs_conconstructor}

```dafny
codatatype D = A | B
function {:abstemious} f(): int {0}
```

<!-- TODO -->
_Abstemious functions are not documented. Please report occurences of this error message._

## **Error: an abstemious function is allowed to invoke a codatatype destructor only on its parameters** {#r_bad_astemious_destructor}

```dafny
codatatype EnormousTree<X> = Node(left: EnormousTree, val: X, right: EnormousTree)
ghost function {:abstemious} BadDestruct(t: EnormousTree): EnormousTree
{ 
  Node(t.left, t.val, t.right.right)  // error: cannot destruct t.right
}   
```

<!-- TODO -->
_Abstemious functions are not documented. Please report occurences of this error message._

## **Error: an abstemious function is allowed to codatatype-match only on its parameters** {#r_bad_astemious_nested_match}

```dafny
codatatype EnormousTree<X> = Node(left: EnormousTree, val: X, right: EnormousTree)
ghost function {:abstemious} BadMatch(t: EnormousTree): EnormousTree
{ 
  match t.right  // error: cannot destruct t.right
  case Node(a, x, b) =>
    Node(a, x, b)
}
```

<!-- TODO -->
_Abstemious functions are not documented. Please report occurences of this error message._

## **Error: an abstemious function is allowed to codatatype-match only on its parameters** {#r_bad_astemious_match}

<!-- TODO - need an example of this variation of error message -->
<!-- TODO -->
_Abstemious functions are not documented. Please report occurences of this error message._

## **Error: an abstemious function is not allowed to check codatatype equality** {#r_bad_astemious_codatatype_equality}

```dafny
codatatype D = A | B(i: bool)
ghost function {:abstemious} f(d: D, e: D): D { B(d == e) }
```

Abstemious functions have some restrictions. One of these is that an abstemious function
may not invoke test of equality over codatatypes, even though this is allowed for
non-abstemious ghost functions.
See the [reference manual](../DafnyRef/DafnyRef#sec-abstemious) for more information on using abstemious functions.


<!-- FILE ./DafnyCore/Resolver/GhostInterestVisitor.cs -->

## **Error: expect statement is not allowed in this context (because this is a ghost method or because the statement is guarded by a specification-only expression)** {#r_expect_statement_is_not_ghost}

<!-- %check-resolve -->
```dafny
method m(ghost b: bool)
{
  var x := 0;
  if b { expect x == 0; }
}
```

`expect` statements are not allowed in ghost contexts; use an `assert` statement instead.
Ghost context can be explicitly clear, such as the body of a method or function declared `ghost`.
But a ghost context can also be implicit, and not so obvious: if part of a statement,
such as the condition of an if statement or loop or the expression being matched in a match 
statement, is ghost, then the rest of the statement may be required to be ghost.

## **Error: print statement is not allowed in this context (because this is a ghost method or because the statement is guarded by a specification-only expression)** {#r_print_statement_is_not_ghost}

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

In addition, methods must be marked with the `{:print}` attribute if 
it has `print` statements or calls methods marked with `{:print}`
and `--track-print-effects` is enabled.
[See the reference manual discussion on :print and tracking print effects](../DafnyRef/DafnyRef#sec-print).

## **Error: ghost-context _kind_ statement is not allowed to _kind_ out of non-ghost _target_** {#r_ghost_break}

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

## **Error: _kind_ statement is not allowed in this context (because it is guarded by a specification-only expression)** {#r_produce_statement_not_allowed_in_ghost}

```dafny
method m() {
  ghost var b: bool := true;
  if b { return; }
}
```

If the condition of a `if` or `match` statement is a ghost expression, then the whole statement is
considered ghost. And then the statement can contain no substatements that are forbidden to be ghost.
`return` and `yield` stastements are never ghost, so they cannot appear in a statement whose guarding
value is ghost.

## **Error: cannot assign to _var_ in a ghost context** {#r_no_assign_to_var_in_ghost}

```dafny
method m(ghost c: int) 
{
  var x := 7;
  if (c == 1) { x :| x < 8; }
}
```

No changes to non-ghost variables may occur in ghost contexts.
Ghost context can be implicit, such as the branches of an if-statement
whose condition is a ghost expression.

## **Error: non-ghost _var_ cannot be assigned a value that depends on a ghost** {#r_no_assign_ghost_to_var}

```dafny
method m(ghost c: int) 
{
  var x := 8;
  x :| x < c;
}
```

In a assign-such-that statement, the LHS gets some value that satisfies the boolean expression on the RHS.
If the LHS is non-ghost, then the RHS must be non-ghost, because non-ghost code may not depend on
ghost code.

## **Error: assumption variable must be of type 'bool'** {#r_assumption_var_must_be_bool}

```dafny
method m() {
  ghost var {:assumption} b: int;
}
```

Variables marked with `{:assumption}` must have bool type.
See [the reference manual](#../DafnyRef/DafnyRef#sec-assumption) for more detail on the use of this attribute.


## **Error: assumption variable must be ghost** {#r_assumption_var_must_be_ghost}

```dafny
method m() {
  var {:assumption} b: bool;
}
```

Variables marked with `{:assumption}` must be ghost.
See [the reference manual](#../DafnyRef/DafnyRef#sec-assumption) for more detail on the use of this attribute.


## **Error: assumption variables can only be declared in a method** {#r_assumption_var_must_be_in_method}

<!-- TODO - not sure this is reachable -->

Variables marked with `{:assumption}` must be declared within methods.
See [the reference manual](#../DafnyRef/DafnyRef#sec-assumption) for more detail on the use of this attribute.


## **Error: in _proof_, calls are allowed only to lemmas** {#r_no_calls_in_proof}

```dafny
method n() {}
method m()
{  
  var i: int;
  assert true by {
    n();
  }
}
```

Proof contexts are blocks of statements that are used to construct a proof.
Examples are the bodies of lemma, the by-blocks of assert-by statements
and calc statements. A proof context is a ghost context.
In ghost context, no methods may be called, even ghost methods.
Only lemmas may be called.

## **Error: only ghost methods can be called from this context** {#r_only_ghost_calls}

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

## **Error: actual out-parameter _parameter_ is required to be a ghost variable** {#r_out_parameter_must_be_ghost}

```dafny
method n() returns (r: int, ghost s: int) {}
method m(a: array<int>) returns (r: bool)
  requires a.Length > 1
{ 
  var x: int;
  var y: int;
  x, y := n();
  a[0] := 0;
}
```

The method being called returns a ghost value as one of its out-parameters.
The variable receiving that value is required to be ghost as well.
Note that out-parameters are numbered beginning with 0.

This message can also arise when the receiving left-hand-side expression
is an array element (e.g. a[0]). This is not permitted at all because
arrays are never ghost.

<!-- 2 instances -->

## **Error: actual out-parameter _parameter_ is required to be a ghost field** {#r_out_parameter_must_be_ghost_field}

```dafny
class A { var a: int }
method n() returns (r: int, ghost s: int) {}
method m(a: A) returns (r: bool)
{ 
  var x: int;
  var y: int;
  x, a.a := n();
}
```

The method being called returns a ghost value as one of its out-parameters.
The left-hand-side expression receiving that value is required to be ghost as well.
In this case, the LHS expression is a field of an object;
the field itself must be ghost, not simply the whole object.
Note that out-parameters are numbered beginning with 0.


## **Error: a loop in _context_ is not allowed to use 'modifies' clauses** {#r_loop_may_not_use_modifies}

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

Proof contexts are blocks of statements that are used to construct a proof.
Examples are the bodies of lemma, the by-blocks of assert-by statements
and calc statements. A proof context is a ghost context. One of the rules
for ghost contexts is that nothing on the heap may be modified in ghost context.
Consequently there is no need for a modifies clause for loops that might
be used to support the proof in the `by` block.

## **Error: 'decreases *' is not allowed on ghost loops** {#r_decreases_forbidden_on_ghost_loops}

<!-- %check-resolve -->
```dafny
method m()
  decreases *
{
  ghost var c := 10;
  while 0 <= c 
    invariant 0 <= c <= 10
    decreases *
  {
    c := c - 1;
  }
}
```

A while loop is ghost if its controlling condition is a ghost expression.
Similarly, a for loop is ghost if the range over which the index variable ranges is ghost.
Ghost code is meant to aid proofs; for sound proofs any constructs in the ghost code must be terminating.
Hence, indications of non-terminating loops, that is, `decreases *`, are not permitted.

This does mean that the specifier has to do the work of designing a valid terminating condition and proving it.

<!-- 3 instances -->

## **Error: a loop in _proof_ is not allowed to use 'modifies' clauses** {#r_loop_in_proof_may_not_use_modifies}

<!-- TODO - this example give r_loop_may_not_use_modifies
<!-- %no-check -->
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
-->

A proof context, such as the body of a lemma, is ghost context and thus is not allowed to modify
anything on the heap. If there is nothing that may be modified, then there is no need for
a `modifies` clause for a loop. Note that the `modifies` clause does not list any local 
variables that are changed in a loop in any case.

<!-- 2 instances -->

## **Error: a ghost loop must be terminating; make the end-expression specific or add a 'decreases' clause** {#r_ghost_loop_must_terminate}

<!-- TODO -->

## **Error: _proof_ is not allowed to perform an aggregate heap update** {#r_no_aggregate_heap_update_in_proof}

```dafny
lemma p(a: array<int>)
{
  forall i | 0 <= i < a.Length { a[i] := 0; } 
}
```

Proof contexts, such as bodies of lemmas or by-blocks, cannot perform any changes to the heap.
In particular that disallows assignments to array elements using a `forall` aggregate update.

## **Error: forall statements in non-ghost contexts must be compilable, but Dafny's heuristics can't figure out how to produce or compile a bounded set of values for '_name_'** {#r_unknown_bounds_for_forall}

<!-- TODO ; this might be shadowed by a similar message in ExpressionTester -->

## **Error: a modify statement is not allowed in _proof_** {#r_modify_forbidden_in_proof}

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

## **Error: _proof_ is not allowed to use 'new'** {#r_new_forbidden_in_proof}

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

## **Error: _proof_ is not allowed to make heap updates** {#r_no_heap_update_in_proof}

```dafny
class A { ghost var k: int }
lemma m(a: A)
{
  a.k := 9;
}
```

An update to a field of a heap object is not allowed in a proof context such as the body of a lemma.
This is the case even if the field in question is a ghost field of its containing class or trait.

## **Error: assignment to _kind_ is not allowed in this context, because _reason_** {#r_assignment_forbidden_in_context}

```dafny
class A { var a: int }
lemma lem(aa: A) {
  aa.a := 1;
}
method m(aa: A) {
  ghost var b := true;
  if b { aa.a := 1; }
}
```

This message can occur in many program situations: the fault is an assignment to a field in the heap
that is not permitted because the assignment statement occurs in a ghost context within a generally
non-ghost environment. A common example is the then or else branch of a `if` statement that is
deemed a ghost context because the controlling condition for the loop is a ghost expression.
Similar situations arise for loops and match statements.

## **Error: the result of a ghost constructor can only be assigned to a ghost variable** {#r_assignment_to_ghost_constructor_only_in_ghost}

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


