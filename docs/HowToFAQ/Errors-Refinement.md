
<!-- %check-resolve %default %useHeadings -->


<!-- FILE ./DafnyCore/Rewriters/RefinementTransformer.cd -->

## **Error: _submod_ in _module_ cannot be imported with "opened" because it does not match the corresponding import in the refinement base _base_.** {#ref_refinement_import_must_match_opened_base}

<!-- TODO -->

## **Error: _submod_ in _module_ must be imported with "opened"  to match the corresponding import in its refinement base _base_.** {#ref_refinement_import_must_match_non_opened_base}

<!-- TODO -->

## **Error: a type synonym (_name_) is not allowed to replace a _kind_ from the refined module (_refined_), even if it denotes the same type** {#ref_refinement_type_must_match_base}

<!-- TODO -->

## **Error: to redeclare and refine declaration '_name_' from module '_refined_', you must use the refining (`...`) notation** {#ref_refining_notation_needed}

<!-- TODO -->

## **Error: declaration '_name_' indicates refining (notation `...`), but does not refine anything** {#ref_refining_notation_does_not_refine}

<!-- TODO -->

## ** Error: can't change if a module export is default (_name_)** {#ref_default_export_unchangeable}

<!-- TODO -->

## **Error: a module (_name_) must refine another module** {#ref_module_must_refine_module}

<!-- TODO -->

## **Error: a module export (_name_) must refine another export** {#ref_export_must_refine_export}

<!-- TODO -->

## **Error: a module (_name_) can only refine a module facade** {#ref_base_module_must_be_facade}

<!-- TODO -->

## **Error: a module ({0}) must refine another module** {#ref_module_must_refine_module_2}

<!-- TODO -->

## **Error: type declaration '_name_' is not allowed to change the requirement of supporting equality** {#ref_mismatched_equality}

<!-- TODO -->

## **Error: type declaration '_name_' is not allowed to change the requirement of supporting auto-initialization** {#ref_mismatched_auto_init}

<!-- TODO -->

## **Error: type declaration '_name_' is not allowed to change the requirement of being nonempty** {#ref_mismatched_nonempty}

<!-- TODO -->

## **Error: a type declaration that requires equality support cannot be replaced by this trait** {#ref_trait_mismatched_equality}

<!-- TODO -->

## **Error: a type declaration that requires equality support cannot be replaced by a codatatype** {#ref_equality_support_precludes_codatatype}

<!-- TODO -->

## **Error: type '_name_', which does not support equality, is used to refine an abstract type with equality support** {#ref_mismatched_type_equality_support}

<!-- TODO -->

## **Error: type '_name', which does not support auto-initialization, is used to refine an abstract type that expects auto-initialization** {#ref_mismatched_type_auto_init}

<!-- TODO -->

## **Error: type '_name_', which may be empty, is used to refine an abstract type expected to be nonempty** {#ref_mismatched_type_nonempty}

<!-- TODO -->

## **Error: a _kind_ (_name_) cannot declare members, so it cannot refine an abstract type with members** {#ref_mismatched_type_with_members}

<!-- TODO -->

## **Error: an abstract type declaration (_name_) in a refining module cannot replace a more specific type declaration in the refinement base** {#ref_mismatched_abstractness}

<!-- TODO -->

## **Error: a _kind_ declaration (_name_) in a refinement module can only refine a _kind_ declaration or replace an abstract type declaration** {#ref_declaration_must_refine}

<!-- TODO -->

## Error: an iterator declaration (_name_) in a refining module cannot replace a different kind of declaration in the refinement base** {#ref_iterator_must_refine_iterator}

<!-- TODO -->

## **Error: a type (_name_) in a refining module may not replace an already defined type (even with the same value)** {#ref_base_type_cannot_be_refined}

<!-- TODO -->

## **Error: a module (_name_) can only be refined by an alias module or a module facade** {#ref_base_module_must_be_abstract_or_alias}

<!-- TODO -->

## **Error: a refining iterator is not allowed to add preconditions** {#ref_no_new_iterator_preconditions}

<!-- TODO -->

## **Error: a refining iterator is not allowed to add yield preconditions** {#ref_no_new_iterator_yield_preconditions}

<!-- TODO -->

## **Error: a refining iterator is not allowed to extend the reads clause** {#ref_no_new_iterator_reads}

<!-- TODO -->

## Error: a refining iterator is not allowed to extend the modifies clause** {#ref_no_new_iterator_modifies}

<!-- TODO -->

## **Error: a refining iterator is not allowed to extend the decreases clause** {#ref_no_new_iterator_decreases}

<!-- TODO -->

## **Error: a const declaration (_name_) in a refining class (_class_) must replace a const in the refinement base** {#ref_const_must_refine_const}

<!-- TODO -->

## **Error: the type of a const declaration (_name_) in a refining class (_class_) must be syntactically the same as for the const being refined** {#ref_no_changed_const_type}

<!-- TODO -->

## **Error: a const re-declaration (_name_) can give an initializing expression only if the const in the refinement base does not** {#ref_no_refining_const_initializer}

<!-- TODO -->

## **Error: a const in a refining module cannot be changed from static to non-static or vice versa: _name_** {#ref_mismatched_module_static}

<!-- TODO -->

## **Error: a const re-declaration (_name_) is not allowed to un-ghostify the const** {#ref_mismatched_const_ghost}

<!-- TODO -->

## **Error: a const re-declaration (_name_) must be to ghostify the const_info_** {#ref_refinement_must_add_const_ghost}

<!-- TODO ; allowed to add an initializer-->

## **Error: a field declaration (_name_) in a refining class (_class_) must replace a field in the refinement base** {#ref_field_must_refine_field}

<!-- TODO -->

## **Error: a field declaration (_name_) in a refining class (_class) must repeat the syntactically same type as the field has in the refinement base** {#ref_mismatched_field_name}

<!-- TODO -->

## **Error: a field re-declaration (_name_) must be to ghostify the field** {#ref_refinement_field_must_add_ghost}

<!-- TODO -->

## **Error: a _kind_ declaration (_name_) can only refine a _kind_** {#ref_mismatched_refinement_kind}

<!-- TODO -->

## Error: a refining _kind_ is not allowed to add preconditions** {#ref_refinement_no_new_preconditions}

<!-- TODO -->

## **Error: a refining _kind_ is not allowed to extend the reads clause** {#ref_refinement_no_new_reads}

<!-- TODO -->

## **Error: decreases clause on refining _kind_ not supported** {#ref_no_new_decreases}

<!-- TODO -->

## **Error: a function in a refining module cannot be changed from static to non-static or vice versa: _name_** {#ref_mismatched_function_static}

<!-- TODO -->

## **Error: a compiled function cannot be changed into a ghost function in a refining module: _name_** {#ref_mismatched_function_compile}

<!-- TODO -->

## **Error: a ghost function can be changed into a compiled function in a refining module only if the function has not yet been given a body: _name_** {#ref_no_refinement_function_with_body}

<!-- TODO -->

## **Error: the name of function return value '_function_'(_result_) differs from the name of corresponding function return value in the module it refines (_otherresult_)** {#ref_mismatched_function_return_name}

<!-- TODO -->

## **Error: the result type of function '_function_' (_type_) differs from the result type of the corresponding function in the module it refines (_othertype_)** {#ref_mismatched_function_return_type}

<!-- TODO -->

## **Error: a refining _kind_ is not allowed to extend/change the body** {#ref_mismatched_refinement_body}

<!-- TODO -->

## Error: a method declaration (_name_) can only refine a method** {#ref_method_refines_method}

<!-- TODO -->

## **Error: a refining method is not allowed to add preconditions** {#ref_no_new_method_precondition}

<!-- TODO -->

## **Error: a refining method is not allowed to extend the modifies clause** {#ref_no_new_method_modifies}

<!-- TODO -->

## **Error: decreases clause on refining method not supported, unless the refined method was specified with 'decreases *'** {#ref_no_new_method_decreases}

<!-- TODO -->

## **Error: a method in a refining module cannot be changed from static to non-static or vice versa: _name_** {#ref_mismatched_method_static}

<!-- TODO -->

## **Error: a method cannot be changed into a ghost method in a refining module: _name_** {#ref_mismatched_method_ghost}

<!-- TODO -->

## **Error: a ghost method cannot be changed into a non-ghost method in a refining module: _name_** {#ref_mismatched_method_non_ghost}

<!-- TODO -->

## **Error: _what_ '_name_' is declared with a different number of type parameters (_count_ instead of _oldcount_) than the corresponding _what_ in the module it refines** {#ref_mismatched_type_parameters_count}

<!-- TODO -->

## **Error: type parameters are not allowed to be renamed from the names given in the _kind_ in the module being refined (expected '_oldname_', found '_name_')** {#ref_mismatched_type_parameter_name}

<!-- TODO -->

## **Error: type parameter '_name_' is not allowed to change the requirement of supporting equality** {#ref_mismatched_type_parameter_equality}

<!-- TODO -->

## **Error: type parameter '_name_' is not allowed to change the requirement of supporting auto-initialization** {#ref_mismatched_type_parameter_auto_init}

<!-- TODO -->

## **Error: type parameter '_name_' is not allowed to change the requirement of being nonempty** {#ref_mismatched_type_parameter_nonempty}

<!-- TODO -->

## Error: type parameter '_name_' is not allowed to change the no-reference-type requirement** {#ref_mismatched_type_parameter_not_reference}

<!-- TODO -->

## **Error: type parameter '_name_' is not allowed to change variance (here, from '_oldvariance_' to '_variance_')** {#ref_mismatched_type_parameter_variance}

<!-- TODO -->

## **Error: _kind_ '_name_' is declared with a different number of _what_ (_num_ instead of _oldnum_) than the corresponding _kind_ in the module it refines** {#ref_mismatched_kind_count}

<!-- TODO -->

## **Error: there is a difference in name of _kind_ _num_ ('_name_' versus '_oldname') of _kind_ _name_ compared to corresponding _kind_ in the module it refines** {#ref_mismatched_kind_name}

<!-- TODO -->

## **Error: _kind_ '_name_' of _kind_ _container_ cannot be changed, compared to the corresponding _kind_ in the module it refines, from non-ghost to ghost** {#ref_mismatched_kind_ghost}

<!-- TODO -->

## **Error: _kind_ '_name_' of _kind_ _container_ cannot be changed, compared to the corresponding _kind_ in the module it refines, from ghost to non-ghost** {#ref_mismatched_kind_non_ghost}

<!-- TODO -->

## **Error: _kind_ '_name_' of _kind_ _container_ cannot be changed, compared to the corresponding _kind_ in the module it refines, from new to non-new** {#ref_mismatched_kind_non_new}

<!-- TODO -->

## **Error: _kind_ '_name_' of _kind_ _container_ cannot be changed, compared to the corresponding _kind_ in the module it refines, from non-new to new** {#ref_mismatched_kind_new}

<!-- TODO -->

## **Error: _kind_ '_name_' of _kind_ _container_ cannot be changed, compared to the corresponding _kind_ in the module it refines, from non-older to older** {#ref_mismatched_kind_older}

<!-- TODO -->

## **Error: _kind_ '_name_' of _kind_ _container_ cannot be changed, compared to the corresponding _kind_ in the module it refines, from older to non-older** {#ref_mismatched_kind_non_older}

<!-- TODO -->

## **Error: the type of _kind_ '_n_' is different from the type of the same _kind_ in the corresponding _thing_ in the module it refines ('_name_' instead of '_oldname_')** {#ref_mismatched_parameter_name}

<!-- TODO -->

## Error: a refining formal parameter ('_name_') in a refinement module is not allowed to give a default-value expression** {#ref_refined_formal_may_not_have_default}

<!-- TODO -->

## **Error: skeleton statement does not match old statement** {#ref_mismatched_skeleton}

<!-- TODO -->

## **Error: assert template does not match inherited statement** {#ref_mismatched_assert}

<!-- TODO -->

## **Error: expect template does not match inherited statement** {#ref_mismatched_expect}

<!-- TODO -->

## **Error: assume template does not match inherited statement** {#ref_mismatched_assume}

<!-- TODO -->

## **Error: if-statement template does not match inherited statement** {#ref_mismatched_if_statement}

<!-- TODO -->

## **Error: while-statement template does not match inherited statement** {#ref_mismatched_while_statement}

<!-- TODO -->

## **Error: a skeleton while statement with a guard can only replace a while statement with a non-deterministic guard** {#ref_mismatched_while_statement_guard}

<!-- TODO -->

## **Error: modify template does not match inherited statement** {#ref_mismatched_modify_statement}

<!-- TODO -->

## **Error: modify template must have a body if the inherited modify statement does** {#ref_mismatched_statement_body}

<!-- TODO -->

## **Error: a refining loop can provide a decreases clause only if the loop being refined was declared with 'decreases *'** {#ref_mismatched_loop_decreases}

<!-- TODO -->

## **Error: while template must have a body if the inherited while statement does** {#ref_mismatched_while_body}

<!-- TODO -->

## **Error: skeleton statement may not be used here; it does not have a matching statement in what is being replaced** {#ref_misplaced_skeleton}

<!-- TODO -->

## **Error: yield statements are not allowed in skeletons** {#ref_misplaced_yield}

<!-- TODO -->

## **Error: _kind_ statement in skeleton is not allowed to break outside the skeleton fragment** {#ref_invalid_break_in_skeleton}

<!-- TODO -->

## Error: cannot have assignment statement** {#ref_misplaced_assignment}

<!-- TODO -->

## **Error: cannot have call statement** {#ref_misplaced_call}

<!-- TODO -->

## **Error: refinement method cannot assign to variable defined in parent module ('_name_')** {#ref_invalid_variable_assignment}

<!-- TODO -->

## **Error: refinement method cannot assign to a field defined in parent module ('{0}')** {#ref_invalid_field_assignment}

<!-- TODO -->

## **Error: new assignments in a refinement method can only assign to state that the module defines (which never includes array elements)** {#ref_invalid_new_assignments}

<!-- TODO -->

## **Error: assignment RHS in refinement method is not allowed to affect previously defined state** {#ref_invalid_assignment_rhs}

<!-- TODO -->

