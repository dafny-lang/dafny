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

## **a _what_ is allowed only in specification contexts**

<!-- TODO -->

## **a _what_ with ghost parameters can be used as a value only in specification contexts**

<!-- TODO -->

## **_what_ '_name_' can be used only in specification contexts**

<!-- TODO -->

## **in a compiled context, update of _deconstructors_ cannot be applied to a datatype value of a ghost variant (ghost constructor _constructor_)**

<!-- TODO -->

## **a call to a _kind_ is allowed only in specification contexts**

<!-- TODO -->

## **a call to a ghost _what_ is allowed only in specification contexts (consider declaring the _what_ without the 'ghost' keyword)**

<!-- TODO -->

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

A datatype can have a mix of non-ghot and ghost constructors, but the ghost constructors
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

## **an expression of type '_type_' is not run-time checkable to be a '_type_'**

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

## **rank comparisons are allowed only in specification and ghost contexts**

<!-- TODO -->

## **prefix equalities are allowed only in specification and ghost contexts**

<!-- TODO -->

## **_what_ in non-ghost contexts must be compilable, but Dafny's heuristics can't figure out how to produce or compile a bounded set of values for '_name_'**

<!-- TODO -->

## **match expression is not compilable, because it depends on a ghost constructor**

<!-- TODO -->


<!-- ./DafnyCore/Resolver/TypeInferenceChecker.cs -->

## **newtype's base type is not fully determined; add an explicit type for '_name_'**

<!-- TODO -->

## **subset type's base type is not fully determined; add an explicit type for '_name_'**

<!-- TODO -->

## **shared destructors must have the same type, but '_name_' has type '_type_' in constructor '_name_' and type '_type_' in constructor '_name_'**

<!-- TODO -->

## **literal (_literal_) is too large for the bitvector type _type_**

<!-- TODO -->

## **unary minus (-{0}, type {1}) not allowed in case pattern**

<!-- TODO -->

## **type of type parameter could not be determined; please specify the type explicitly**

<!-- TODO -->

## **type of bound variable '{bv.Name}' could not be determined; please specify the type explicitly**

<!-- TODO -->

## **type of bound variable '{bv.Name}' ('{bv.Type}') is not allowed to use type ORDINAL**

<!-- TODO -->

## **Warning: the quantifier has the form 'exists x :: A ==> B', which most often is a typo for 'exists x :: A && B'; if you think otherwise, rewrite as 'exists x :: (A ==> B)' or 'exists x :: !A || B' to suppress this warning**

<!-- TODO -->

## **type parameter '{tp.Name}' (inferred to be '{p}') to the {e.Member.WhatKind} '{e.Member.Name}' could not be determined**

<!-- TODO -->

## **type parameter '{tp.Name}' (passed in as '{p}') to the {e.Member.WhatKind} '{e.Member.Name}' is not allowed to use ORDINAL**

<!-- TODO -->

## **type parameter '{tp.Name}' (inferred to be '{p}') in the function call to '{e.Name}' could not be determined**

<!-- TODO -->

## **type parameter '{tp.Name}' (inferred to be '{p}') in the function call to '{e.Name}' could not be determined. If you are making an opaque function, make sure that the function can be called.**

<!-- TODO -->

## **type parameter '{tp.Name}' (passed in as '{p}') to function call '{e.Name}' is not allowed to use ORDINAL**

<!-- TODO -->

## **the type of the bound variable '{x.Name}' could not be determined**

<!-- TODO -->

## **a type cast to a reference type ({0}) must be from a compatible type (got {1}); this cast could never succeed**

<!-- TODO -->

## **a type test to '{0}' must be from a compatible type (got '{1}')**

<!-- TODO -->

## **a non-trivial type test is allowed only for reference types (tried to test if '{1}' is a '{0}')**

<!-- TODO -->

## **Warning: the type of the other operand is a non-null type, so this comparison with 'null' will always return '{b}'**

<!-- TODO -->

## **Warning: the type of the other operand is a non-null type, so this comparison with 'null' will always return '{b}' (to make it possible for {name} to have the value 'null', declare its type to be '{ty}')**
<!-- TODO -->


## **Warning: the type of the other operand is a {what} of non-null elements, so the {non}inclusion test of 'null' will always return '{b}'**

<!-- TODO -->

## **Warning: the type of the other operand is a map to a non-null type, so the inclusion test of 'null' will always return '{b}'**

<!-- TODO -->

## **the type of this {0} is underspecified**

<!-- TODO -->

## **an ORDINAL type is not allowed to be used as a type argument**

<!-- TODO -->


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
But a ghost context can also be implicit, and not so obvious: if part of a statement,
such as the condition of an if statement or loop or the expression being matched in a match 
statement, is ghost the rest of the statement may be required to be ghost.

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

## **a loop in _proof_ is not allowed to use 'modifies' clauses**

<!-- TODO -->

## **a ghost loop must be terminating; make the end-expression specific or add a 'decreases' clause**

<!-- TODO -->

## **_proof_ is not allowed to perform an aggregate heap update**

<!-- TODO -->

## **forall statements in non-ghost contexts must be compilable, but Dafny's heuristics can't figure out how to produce or compile a bounded set of values for '{0}'**

<!-- TODO -->

## **a modify statement is not allowed in _proof_**

<!-- TODO -->

## **_proof_ is not allowed to use 'new'**

<!-- TODO -->

## **_proof_ is not allowed to make heap updates**

<!-- TODO -->

## **assignment to _kind_ is not allowed in this context, because this is a ghost _thing_**

<!-- TODO -->

## **assignment to _kind_ is not allowed in this context, because the statement is in a ghost context; e.g., it may be guarded by a specification-only expression**

<!-- TODO -->

## **the result of a ghost constructor can only be assigned to a ghost variable**

<!-- TODO -->


<!-- ./DafnyCore/Resolver/TypeConstraint.cs-->

<!-- TODO: collector for other errors? -->

<!-- ./DafnyCore/Resolver/TailRecursion.cs -->

<!-- TODO -->

<!-- ./DafnyCore/Resolver/Resolver.cs -->

<!-- TODO Lots -->

