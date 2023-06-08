
<!-- %check-resolve %default %useHeadings -->


<!-- FILE ./DafnyCore/Rewriters/RefinementTransformer.cd -->

## **Error: _submod_ in _module_ cannot be imported with "opened" because it does not match the corresponding import in the refinement base _base_.** {#ref_refinement_import_must_match_opened_base}

<!-- TODO -->

## **Error: _submod_ in _module_ must be imported with "opened"  to match the corresponding import in its refinement base _base_.** {#ref_refinement_import_must_match_non_opened_base}

<!-- TODO -->

## **Error: a type synonym (_name_) is not allowed to replace a _kind_ from the refined module (_refined_), even if it denotes the same type** {#ref_refinement_type_must_match_base}

```dafny
module P {
  type T = int
}
module Q refines P {
  type T = int
}
```

A refining declaration must make the base declaration more specific. It may not just be the same declaration (although sometimes that might be convenient).

## **Error: to redeclare and refine declaration '_name_' from module '_refined_', you must use the refining (`...`) notation** {#ref_refining_notation_needed}

<!-- TODO -->

## **Error: declaration '_name_' indicates refining (notation `...`), but does not refine anything** {#ref_refining_notation_does_not_refine}

```dafny
module P {
}
module Q refines P {
  export A ...
}
```

A refining declaration that uses `...` must actually be refining a corresponding declaration in the base module.

## **Error: can't change if a module export is default (_name_)** {#ref_default_export_unchangeable}

```dafny
module P {
  const c: int
  export reveals c
}
module Q refines P {
  export P ...
}
```

If a base module P has a default export (implicitly named P), then a refining module, Q, may not declare an export set P with the intention of refining it.

## **Error: a module (_name_) must refine another module** {#ref_module_must_refine_module}

<!-- TODO -->

## **Error: a module export (_name_) must refine another export** {#ref_export_must_refine_export}

<!-- TODO -- suspect not reachable -->

## **Error: a module (_name_) can only refine a module facade** {#ref_base_module_must_be_facade}

<!-- TODO -->

## **Error: a module (_name_) must refine another module** {#ref_module_must_refine_module_2}

```dafny
module P {
  type W
}
module Q refines P {
  module W {}
}
```

A submodule M within a module that is refining some base module must refine some submodule M in the base module.

## **Error: type declaration '_name_' is not allowed to change the requirement of supporting equality** {#ref_mismatched_equality}

<!-- TODO -->

## **Error: type declaration '_name_' is not allowed to change the requirement of supporting auto-initialization** {#ref_mismatched_auto_init}

<!-- TODO -->

## **Error: type declaration '_name_' is not allowed to change the requirement of being nonempty** {#ref_mismatched_nonempty}

<!-- TODO -->

## **Error: a type declaration that requires equality support cannot be replaced by this trait** {#ref_trait_mismatched_equality}

<!-- TODO -->

## **Error: a type declaration that requires equality support cannot be replaced by a codatatype** {#ref_equality_support_precludes_codatatype}

```dafny
module P {
  type T(==)
}
module Q refines P {
  codatatype T = A
}
```

Codatatypes do not generally support equality and so cannot be refinements of an abstract type that declares that it supports equality.

## **Error: type '_name_', which does not support equality, is used to refine an abstract type with equality support** {#ref_mismatched_type_equality_support}

```dafny
module P {
  type T(==)
}
module Q refines P {
  codatatype A = B | C
  type T = A
}
```

A refining type must be declared to support equality (with `(==)`) if the base declaration is declared to support equality.


## **Error: type '_name_', which does not support auto-initialization, is used to refine an abstract type that expects auto-initialization** {#ref_mismatched_type_auto_init}

```dafny
module P {
  type T(0)
}
module Q refines P {
  class A{}
  type T = A
}
```

A refining type must be declared to be auto-initializing (with `(0)`) if the base declaration is declared auto-initializing.


## **Error: type '_name_', which may be empty, is used to refine an abstract type expected to be nonempty** {#ref_mismatched_type_nonempty}

```dafny
module P {
  type T(00)
}
module Q refines P {
  class A{}
  type T = A
}
```

A refining type must be declared to be non-empty (with `(00)`) if the base declaration is declared non-empty.

## **Error: a _kind_ (_name_) cannot declare members, so it cannot refine an abstract type with members** {#ref_mismatched_type_with_members}

```dafny
module P {
  type T {
    method m() {}
  }
}
module Q refines P {
  type T = int
}
```

When refining a declaration, the refined declaration has all the characteristics of the base declaration, including any members of the base declaration.
Some declarations do not have members, such as subset types and type synonyms, so they cannot refine a declaration that has members declared in the base.

## **Error: an abstract type declaration (_name_) in a refining module cannot replace a more specific type declaration in the refinement base** {#ref_mismatched_abstractness}

```dafny
module P {
  type T = int
}
module Q refines P {
  type T ...
}
```

The purpose of refinement is to replace abstract or incompletely defined declarations with more specific declarations.
Hence a type that is defined in a refinement base cannot be an abstract type in the refining module.

## **Error: a _kind_ declaration (_name_) in a refinement module can only refine a _kind_ declaration or replace an abstract type declaration** {#ref_declaration_must_refine}

```dafny
module P {
  type T = int
}
module Q refines P {
  datatype T ... {}
}
```

The purpose of refinement is to replace abstract or incompletely defined declarations with more specific declarations.
The refining declaration needs to be the same kind of declaration as in the base.


## **Error: an iterator declaration (_name_) in a refining module cannot replace a different kind of declaration in the refinement base** {#ref_iterator_must_refine_iterator}

<!-- %check-resolve %first -->
```dafny
module P {
  class I {}
}
module Q refines P {
  iterator I...
}
```

Iterators may only refine iterator declarations.

## **Error: a type (_name_) in a refining module may not replace an already defined type (even with the same value)** {#ref_base_type_cannot_be_refined}

<!-- TODO - does not appear to be reachable -->

## **Error: a module (_name_) can only be refined by an alias module or a module facade** {#ref_base_module_must_be_abstract_or_alias}

<!-- TODO  - not sure this is reachable-->

## **Error: a refining iterator is not allowed to add preconditions** {#ref_no_new_iterator_preconditions}

```dafny
module P {
  iterator I() yields (x: int)
}
module Q refines P {
  iterator I... requires true
}
```

There are restrictions on what may change when refining an iterator. In particular, no new preconditions may be added
even if they are implied by the base declarations's preconditions.

## **Error: a refining iterator is not allowed to add yield preconditions** {#ref_no_new_iterator_yield_preconditions}

```dafny
module P {
  iterator I() yields (x: int)
}
module Q refines P {
  iterator I... yield requires true
}
```

There are restrictions on what may change when refining an iterator. In particular, no new yield preconditions may be added
even if they are implied by the base declarations's preconditions.


## **Error: a refining iterator is not allowed to extend the reads clause** {#ref_no_new_iterator_reads}

```dafny
module P {
  iterator I() yields (x: int)
}
module Q refines P {
  iterator I... reads {}
}
```

There are restrictions on what may change when refining an iterator. In particular, no new reads clauses may be added
even if they are contained within the base declarations's reads clauses.


## **Error: a refining iterator is not allowed to extend the modifies clause** {#ref_no_new_iterator_modifies}

```dafny
module P {
  iterator I() yields (x: int)
}
module Q refines P {
  iterator I... modifies {}
}
```

There are restrictions on what may change when refining an iterator. In particular, no new modifies clauses may be added
even if they list objects that are contained within the base declarations's modifies clauses.


## **Error: a refining iterator is not allowed to extend the decreases clause** {#ref_no_new_iterator_decreases}

```dafny
module P {
  iterator I() yields (x: int)
}
module Q refines P {
  iterator I... decreases 1 {}
}
```

There are restrictions on what may change when refining an iterator. In particular, no new decreases clause may be added
even if it is the same as or implied by the base declaration's decreases clause.


## **Error: a const declaration (_name_) in a refining class (_class_) must replace a const in the refinement base** {#ref_const_must_refine_const}

```dafny
module P {
  class A { var c: int }
}
module Q refines P {
  class A ... { const c: int }
}
```

Following the general rule that declarations in the base module are replaced by more specific declarations of the same kind in the refining module,
a `const` declaration in the refining module must replace a `const` declaration in the base module (with the same type).

## **Error: the type of a const declaration (_name_) in a refining class (_class_) must be syntactically the same as for the const being refined** {#ref_no_changed_const_type}

```dafny
module P {
  type T = bool
  class A { const c: bool }
}
module Q refines P {
  class A ... { const c: T }
}
```

The declarations in a refining module must have the same type as in the base module. In fact, to enable easier checking that the type
has not changed, the type must be expressed in the same syntactic form in the two declarations. For example, it is not permitted to use a type in a base declaration and 
an equivalent type synonym for the corresponding variable in the refinement.

## **Error: a const re-declaration (_name_) can give an initializing expression only if the const in the refinement base does not** {#ref_no_refining_const_initializer}

```dafny
module P {
  const c := 7
}
module Q refines P {
  const c := 8
}
```

A refined declaration of a `const` may add an initializer, but it cannot replace an initializer declared in the base,
even if it is syntactically the same value, such as an explicit literal in one place and an equivalent expression in the other.

## **Error: a const in a refining module cannot be changed from static to non-static or vice versa: _name_** {#ref_mismatched_module_static}

```dafny
module P {
 class A {const c: int }
}
module Q refines P {
  class A ... { static const c := 7 }
}
```

A `const` declaration that is in a class that is being refined cannot change its static-ness.

## **Error: a const re-declaration (_name_) is not allowed to remove 'ghost' from the const declaration** {#ref_mismatched_const_ghost}

```dafny
module P {
  ghost const c := 7
}
module Q refines P {
  const c: int
}
```

A `const` refining declaration cannot change the declaration from `ghost` to non-ghost.

## **Error: a const re-declaration (_name_) must be to add 'ghost' to the const declaration_info_** {#ref_refinement_must_add_const_ghost}

```dafny
module P {
  const c := 7
}
module Q refines P {
  const c: int
}
```

A `const` refinement must change something. It can add a `ghost` modifier or it can add an initializer.

## **Error: a field declaration (_name_) in a refining class (_class_) must replace a field in the refinement base** {#ref_field_must_refine_field}

```dafny
module P {
  type T = int
  class A { const c: int }
}
module Q refines P {
  class A ... { var c: T }
}
```

Following the general rule that declarations in the base module are replaced by more specific declarations of the same kind in the refining module,
a `var` declaration in a refining class must replace a `var` declaration in the class of the base module (with the same type).


## **Error: a field declaration (_name_) in a refining class (_class_) must repeat the syntactically same type as the field has in the refinement base** {#ref_mismatched_field_name}

```dafny
module P {
  type T = int
  class A { var c: int }
}
module Q refines P {
  class A ... { var c: T }
}
```

The field declarations in a refining class must have the same type as in the class in the base module. In fact, to enable easier checking that the type
has not changed, the type must be expressed in the same syntactic form in the two declarations. For example, it is not permitted to use a type 
in a base declaration and an equivalent type synonym in the corresponding place in the refinement.


## **Error: a field re-declaration (_name_) must be to add 'ghost' to the field declaration** {#ref_refinement_field_must_add_ghost}

```dafny
module P {
  class A { var c: int }
}
module Q refines P {
  class A ... { var c: int }
}
```

When a class is being refined, any field declaration in the base is copied into the refinement.
If there is a redeclaration of the field, it must be to add a `ghost` modifier.

## **Error: a _kind_ declaration (_name_) can only refine a _kind_** {#ref_mismatched_refinement_kind}

```dafny
module P {
  function f(i: int): bool
}
module Q refines P {
  predicate f(i: int) { true }
}
```

The refining declaration must be the same kind of declaration as the base declaration.
For example both must be predicates or both must be functions (even if the function is one that returns a `bool`).

## **Error: a refining _kind_ is not allowed to add preconditions** {#ref_refinement_no_new_preconditions}

```dafny
module P {
  predicate m(i: nat)
}
module Q refines P {
  predicate m(i: nat) requires true { true }
}
```

A function in a refining module must be able to be used in the same way as the abstract function in the base module.
If there are additional preconditions, then the call contexts for the refined function may be more restricted than for the base function.
Thus no new preconditions may be added. This is a syntactic check, so no preconditions can be added even if they
are implied by the existing preconditions.

## **Error: a refining _kind_ is not allowed to extend the reads clause** {#ref_refinement_no_new_reads}

```dafny
module P {
  predicate m() reads {}
}
module Q refines P {
  predicate m() reads this {true }
}
```

A function in a refining module must be able to be used in the same way as the abstract function in the base module.
Extending the reads clause with additional objects cxhanges this equivalence and is not allowed.
This change is syntactic. The refining function is not allowed to write any reads clauses. It just inherits those from
the base declaration. This is the case even if the new reads clause is a repetition or subset of the base declaration.

## **Error: decreases clause on refining _kind_ not supported** {#ref_no_new_decreases}

```dafny
module P {
  predicate m(i: nat) reads {}
}
module Q refines P {
  predicate m(i: nat) decreases i {true }
}
```

For simplicity, a refining function is not allowed to add decreases clauses to its declaration.

## **Error: a function in a refining module cannot be changed from static to non-static or vice versa: _name_** {#ref_mismatched_function_static}

```dafny
module P {
  class A { predicate m(i: nat) }
}
module Q refines P {
  class A ... { static predicate m(i: nat) {true } }
}
```

The static-ness of a function declaration in a refining class must be the same as in the base class.

## **Error: a compiled function cannot be changed into a ghost function in a refining module: _name_** {#ref_mismatched_function_compile}

```dafny
module P {
  predicate m(i: nat)
}
module Q refines P {
  ghost predicate m(i: nat)
}
```

If a function is declared as non-ghost in the base module, it may not be declared `ghost` in the refining module.

## **Error: a ghost function can be changed into a compiled function in a refining module only if the function has not yet been given a body: _name_** {#ref_no_refinement_function_with_body}

<!-- %check-resolve %first -->
```dafny
module P {
  ghost predicate m(i: nat) { true }
}
module Q refines P {
  predicate m(i: nat) { true }
}
```

If a function is declared ghost in a base module, it can then be given a body and declared non-ghost in the refined version of the module.
But in the case where the the base declaration already has a body and is `ghost`, the refined declaration cannot then change the function to non-ghost.

## **Error: the name of function return value '_function_'(_result_) differs from the name of corresponding function return value in the module it refines (_otherresult_)** {#ref_mismatched_function_return_name}

```dafny
module P {
  function f(a: int): (r: int)
}
module Q refines P {
  function f(a: int): (s: int) { 0 }
}
```

When refining a function, the input and output signature must stay precisely the same -- formals, types, and names -- including the name of the function result.


## **Error: the result type of function '_function_' (_type_) differs from the result type of the corresponding function in the module it refines (_othertype_)** {#ref_mismatched_function_return_type}

```dafny
module P {
  function f(a: int): int { 0 }
}
module Q refines P {
  function f(a: int): bool
}
```

When refining a function, the input and output signature must stay precisely the same -- formals, types, and names --
including the type of the function result. The types must be syntactically identical; it is not allowed
to use a type and an equivalent type synonym, for example.

## **Error: a refining _kind_ is not allowed to extend/change the body** {#ref_mismatched_refinement_body}

```dafny
module P {
  function f(a: int): int { 0 }
}
module Q refines P {
  function f(a: int): int { 0 }
}
```

When refining a function, the refining declaration can not include a body if the base declaration has a body, even if the texts of the bodies are identical.

## **Error: a method declaration (_name_) can only refine a method** {#ref_method_refines_method}

```dafny
module P {
  function m(a: int): int
}
module Q refines P {
  method m(a: int)  {}
}
```

The refining declaration must be the same kind of declaration as the base declaration.
For example both must be methods.


## **Error: a refining method is not allowed to add preconditions** {#ref_no_new_method_precondition}

```dafny
module P {
  method m() {}
}
module Q refines P {
  method m() requires true {}
}
```

A method in a refining module must be able to be used in the same way as the abstract method in the base module.
If there are additional preconditions, then the calling contexts permitted for the refined method may be more restricted than those for the abstract base method.
Thus no new preconditions may be added. This is a syntactic check, so no preconditions can be added even if they
are implied by the existing preconditions.


## **Error: a refining method is not allowed to extend the modifies clause** {#ref_no_new_method_modifies}

```dafny
module P {
  method m(i: nat)
}
module Q refines P {
  method m(i: nat) modifies {} { }
}
```

A method in a refining module must be able to be used in the same way as the abstract method in the base module.
If there are additional objects in the modifies clause, then the usage of the refined module may have more effect than known by the base method signature.
Thus no new modifies clauses may be added. This is a syntactic check, so no modifies clauses can be added even if they
do not actually add any new objects to the modifies set.

## **Error: decreases clause on refining method not supported, unless the refined method was specified with 'decreases *'** {#ref_no_new_method_decreases}

```dafny
module P {
  method m(a: int)
}
module Q refines P {
  method m(a: int) decreases a {}
}
```

A decreases clause is not permitted in a refining method declaration, even if it is syntactically identical to the clause in the base declaration.
The one exception is that if the base declares `decreases *` then the refinement may give a decreases clause (even `decreases`*`).
Note that if the refining declaration does not state a decreases clause (the usual case), the refining declaration gets a copy of the base declarations clause.

## **Error: a method in a refining module cannot be changed from static to non-static or vice versa: _name_** {#ref_mismatched_method_static}

```dafny
module P {
  class A { method m(i: nat) }
}
module Q refines P {
  class A ... { static method m(i: nat) { } }
}
```

There are restrictions on what can be changed in a refinement. In particular, a basic characteristic like being or not being `static`
may not change for any kind of declaration.

## **Error: a ghost method cannot be changed into a non-ghost method in a refining module: _name_** {#ref_mismatched_method_non_ghost}

```dafny
module P {
  ghost method m(i: nat) 
}
module Q refines P {
  method m(i: nat) { } 
}
```

There are restrictions on what can be changed in a refinement. In particular, a basic characteristic like being or not being `ghost`
may not change for methods.

## **Error: a method cannot be changed into a ghost method in a refining module: _name_** {#ref_mismatched_method_ghost}

```dafny
module P {
  method m(i: nat) 
}
module Q refines P {
  ghost method m(i: nat) { } 
}
```

There are restrictions on what can be changed in a refinement. In particular, a basic characteristic like being or not being `ghost`
may not change for methods.


## **Error: _what_ '_name_' is declared with a different number of type parameters (_count_ instead of _oldcount_) than the corresponding _what_ in the module it refines** {#ref_mismatched_type_parameters_count}

```dafny
module P {
  method m<T>(i: nat) 
}
module Q refines P {
  method m<T,U>(i: nat) { } 
}
```

There are restrictions on what can be changed in a refinement. In particular, a basic characteristic like the number of type parameters
may not change for any declaration.


## **Error: type parameters are not allowed to be renamed from the names given in the _kind_ in the module being refined (expected '_oldname_', found '_name_')** {#ref_mismatched_type_parameter_name}

```dafny
module P {
  method m<T,U>(i: nat) 
}
module Q refines P {
  method m<T,W>(i: nat) { } 
}
```

There are restrictions on what can be changed in a refinement. 
In particular, for convenience and readability, the names of type parameters
may not change for any declaration.

## **Error: type parameter '_name_' is not allowed to change the requirement of supporting equality** {#ref_mismatched_type_parameter_equality}

```dafny
module P {
  method m<T,U(==)>(i: nat) 
}
module Q refines P {
  method m<T,U>(i: nat) { } 
}
```

There are restrictions on what can be changed in a refinement. 
In particular, any characteristics of type parameters must remain the same.

## **Error: type parameter '_name_' is not allowed to change the requirement of supporting auto-initialization** {#ref_mismatched_type_parameter_auto_init}

```dafny
module P {
  method m<T,U(0)>(i: nat) 
}
module Q refines P {
  method m<T,U>(i: nat) { } 
}
```

There are restrictions on what can be changed in a refinement. 
In particular, any characteristics of type parameters must remain the same.

## **Error: type parameter '_name_' is not allowed to change the requirement of being nonempty** {#ref_mismatched_type_parameter_nonempty}

```dafny
module P {
  method m<T,U(00)>(i: nat) 
}
module Q refines P {
  method m<T,U>(i: nat) { } 
}
```

There are restrictions on what can be changed in a refinement. 
In particular, any characteristics of type parameters must remain the same.


## **Error: type parameter '_name_' is not allowed to change the no-reference-type requirement** {#ref_mismatched_type_parameter_not_reference}

```dafny
module P {
  method m<T,U(!new)>(i: nat) 
}
module Q refines P {
  method m<T,U>(i: nat) { } 
}
```

There are restrictions on what can be changed in a refinement. 
In particular, any characteristics of type parameters must remain the same.


## **Error: type parameter '_name_' is not allowed to change variance (here, from '_oldvariance_' to '_variance_')** {#ref_mismatched_type_parameter_variance}

```dafny
module P {
  type T<+U> 
}
module Q refines P {
  type T<U> = int
}
```

There are restrictions on what can be changed in a refinement. 
In particular, the variance of type parameters must remain the same.


## **Error: _kind_ '_name_' is declared with a different number of _what_ (_num_ instead of _oldnum_) than the corresponding _kind_ in the module it refines** {#ref_mismatched_kind_count}

```dafny
module P {
  method m(i: int)
}
module Q refines P {
  method m(i: int, j: int) {}
}
```

There are restrictions on what can be changed in a refinement. 
In particular, the number, type and names of formal parameters must remain the same.

## **Error: there is a difference in name of _kind_ _num_ ('_name_' versus '_oldname_') of _kind_ _name_ compared to corresponding _kind_ in the module it refines** {#ref_mismatched_kind_name}

```dafny
module P {
  method m(i: int)
}
module Q refines P {
  method m(j: int) {}
}
```

There are restrictions on what can be changed in a refinement. 
In particular, for convenience and readability, the names of formal parameters
may not change for any declaration.


## **Error: _kind_ '_name_' of _kind_ _container_ cannot be changed, compared to the corresponding _kind_ in the module it refines, from non-ghost to ghost** {#ref_mismatched_kind_ghost}

```dafny
module P {
  method m(i: int)
}
module Q refines P {
  method m(ghost i: int) {}
}
```

There are restrictions on what can be changed in a refinement. 
In particular, ghost-ness of formal parameters
may not change for any declaration.

## **Error: _kind_ '_name_' of _kind_ _container_ cannot be changed, compared to the corresponding _kind_ in the module it refines, from ghost to non-ghost** {#ref_mismatched_kind_non_ghost}

```dafny
module P {
  method m(ghost i: int)
}
module Q refines P {
  method m(i: int) {}
}
```

There are restrictions on what can be changed in a refinement. 
In particular, ghost-ness of formal parameters
may not change for any declaration.

## **Error: _kind_ '_name_' of _kind_ _container_ cannot be changed, compared to the corresponding _kind_ in the module it refines, from new to non-new** {#ref_mismatched_kind_non_new}

<!-- TODO -->

## **Error: _kind_ '_name_' of _kind_ _container_ cannot be changed, compared to the corresponding _kind_ in the module it refines, from non-new to new** {#ref_mismatched_kind_new}

<!-- TODO -->

## **Error: _kind_ '_name_' of _kind_ _container_ cannot be changed, compared to the corresponding _kind_ in the module it refines, from non-older to older** {#ref_mismatched_kind_older}

```dafny
module P {
  class A {}
  predicate m(a: A)
}
module Q refines P {
  predicate m(older a: A) { true }
}
```

When refining a predicate, a formal parameter may not change from older to non-older or vice versa.

## **Error: _kind_ '_name_' of _kind_ _container_ cannot be changed, compared to the corresponding _kind_ in the module it refines, from older to non-older** {#ref_mismatched_kind_non_older}

```dafny
module P {
  class A {}
  predicate m(older a: A)
}
module Q refines P {
  predicate m(a: A) { true }
}
```

When refining a predicate, a formal parameter may not change from older to non-older or vice versa.

## **Error: the type of _kind_ '_n_' is different from the type of the same _kind_ in the corresponding _thing_ in the module it refines ('_name_' instead of '_oldname_')** {#ref_mismatched_parameter_type}

```dafny
module P {
  method m(a: bool)
}
module Q refines P {
  method m(a: int) {}
}
```

The types in a signature in a refining declaration must be the same as the corresponding types in the base declaration.
The types must be syntactically identical. For example one cannot be a type synonym of the other.

## **Error: a refining formal parameter ('_name_') in a refinement module is not allowed to give a default-value expression** {#ref_refined_formal_may_not_have_default}

```dafny
module P {
  method m(i: int)
}
module Q refines P {
  method m(i: int := 9) {}
}
```

There are restrictions on what changes can be made in refining a base declaration. 
When refining methods, one restriction is that the refining declaration may not have default value declarations.
The refining method has precisely the same default values as the base declaration.

## **Error: skeleton statement does not match old statement** {#ref_mismatched_skeleton}

_Refining statements are no longer supported in Dafny._

## **Error: assert template does not match inherited statement** {#ref_mismatched_assert}

_Refining statements are no longer supported in Dafny._

## **Error: expect template does not match inherited statement** {#ref_mismatched_expect}

_Refining statements are no longer supported in Dafny._

## **Error: assume template does not match inherited statement** {#ref_mismatched_assume}

_Refining statements are no longer supported in Dafny._

## **Error: if-statement template does not match inherited statement** {#ref_mismatched_if_statement}

_Refining statements are no longer supported in Dafny._

## **Error: while-statement template does not match inherited statement** {#ref_mismatched_while_statement}

_Refining statements are no longer supported in Dafny._

## **Error: a skeleton while statement with a guard can only replace a while statement with a non-deterministic guard** {#ref_mismatched_while_statement_guard}

_Refining statements are no longer supported in Dafny._

## **Error: modify template does not match inherited statement** {#ref_mismatched_modify_statement}

_Refining statements are no longer supported in Dafny._

## **Error: modify template must have a body if the inherited modify statement does** {#ref_mismatched_statement_body}

_Refining statements are no longer supported in Dafny._

## **Error: a refining loop can provide a decreases clause only if the loop being refined was declared with 'decreases *'** {#ref_mismatched_loop_decreases}

_Refining statements are no longer supported in Dafny._

## **Error: while template must have a body if the inherited while statement does** {#ref_mismatched_while_body}

_Refining statements are no longer supported in Dafny._

## **Error: skeleton statement may not be used here; it does not have a matching statement in what is being replaced** {#ref_misplaced_skeleton}

_Refining statements are no longer supported in Dafny._

## **Error: yield statements are not allowed in skeletons** {#ref_misplaced_yield}

_Refining statements are no longer supported in Dafny._

## **Error: _kind_ statement in skeleton is not allowed to break outside the skeleton fragment** {#ref_invalid_break_in_skeleton}

_Refining statements are no longer supported in Dafny._

## **Error: cannot have assignment statement** {#ref_misplaced_assignment}

_Refining statements are no longer supported in Dafny._

## **Error: cannot have call statement** {#ref_misplaced_call}

_Refining statements are no longer supported in Dafny._

## **Error: refinement method cannot assign to variable defined in parent module ('_name_')** {#ref_invalid_variable_assignment}

_Refining statements are no longer supported in Dafny._

## **Error: refinement method cannot assign to a field defined in parent module ('{0}')** {#ref_invalid_field_assignment}

_Refining statements are no longer supported in Dafny._

## **Error: new assignments in a refinement method can only assign to state that the module defines (which never includes array elements)** {#ref_invalid_new_assignments}

_Refining statements are no longer supported in Dafny._

## **Error: assignment RHS in refinement method is not allowed to affect previously defined state** {#ref_invalid_assignment_rhs}

_Refining statements are no longer supported in Dafny._

