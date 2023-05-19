// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System.Collections.Generic;
using static Microsoft.Dafny.ErrorRegistry;

namespace Microsoft.Dafny.Compilers;

public class CompilerErrors {

  public enum ErrorId {
    None,
    c_process_exit,
    c_process_failed_to_start,
    c_unsupported_feature,
    c_abstract_type_needs_hint,
    c_abstract_type_cannot_be_compiled,
    c_iterators_are_not_deterministic,
    c_iterator_has_no_body,
    c_constructorless_class_forbidden,
    c_method_may_not_be_main_method,
    c_could_not_find_stipulated_main_method,
    c_more_than_one_main_method,
    c_method_not_permitted_as_main,
    c_more_than_one_Main_method,
    c_Main_method_not_permitted,
    c_function_has_no_body,
    c_test_function_must_be_compilable,
    c_invalid_synthesize_method,
    c_method_has_no_body,
    c_assume_statement_may_not_be_compiled,
    c_forall_statement_has_no_body,
    c_loop_has_no_body,
    c_nondeterminism_forbidden,
    c_assign_such_that_forbidden,
    c_assign_such_that_is_too_complex,
    c_nondeterministic_if_forbidden,
    c_binding_if_forbidden,
    c_case_based_if_forbidden,
    c_non_deterministic_loop_forbidden,
    c_case_based_loop_forbidden,
    c_no_assignments_to_seven_d_arrays,
    c_bodyless_modify_statement_forbidden,
    c_let_such_that_is_too_complex,
    c_possibly_unsatisfied_postconditions,
    c_stubbing_fields_not_recommended,
    c_abstract_type_cannot_be_compiled_extern,
    c_Go_unsupported_field,
    c_Go_infeasible_conversion,
  }

  static CompilerErrors() {

    Add(ErrorId.c_process_exit,
    @"
");

    Add(ErrorId.c_process_failed_to_start,
    @"
");

    Add(ErrorId.c_unsupported_feature,
    @"
");

    Add(ErrorId.c_abstract_type_needs_hint,
    @"
");

    Add(ErrorId.c_abstract_type_cannot_be_compiled,
    @"
");

    Add(ErrorId.c_iterators_are_not_deterministic,
    @"
");

    Add(ErrorId.c_iterator_has_no_body,
    @"
");

    Add(ErrorId.c_constructorless_class_forbidden,
    @"
");

    Add(ErrorId.c_method_may_not_be_main_method,
    @"
");

    Add(ErrorId.c_could_not_find_stipulated_main_method,
    @"
");

    Add(ErrorId.c_more_than_one_main_method,
    @"
");

    Add(ErrorId.c_method_not_permitted_as_main,
    @"
");

    Add(ErrorId.c_more_than_one_Main_method,
    @"
");

    Add(ErrorId.c_Main_method_not_permitted,
    @"
");

    Add(ErrorId.c_function_has_no_body,
    @"
");

    Add(ErrorId.c_test_function_must_be_compilable,
    @"
");

    Add(ErrorId.c_invalid_synthesize_method,
    @"
");

    Add(ErrorId.c_method_has_no_body,
    @"
");

    Add(ErrorId.c_assume_statement_may_not_be_compiled,
    @"
");

    Add(ErrorId.c_forall_statement_has_no_body,
    @"
");

    Add(ErrorId.c_loop_has_no_body,
    @"
");

    Add(ErrorId.c_nondeterminism_forbidden,
    @"
");

    Add(ErrorId.c_assign_such_that_forbidden,
    @"
");

    Add(ErrorId.c_assign_such_that_is_too_complex,
    @"
");

    Add(ErrorId.c_nondeterministic_if_forbidden,
    @"
");

    Add(ErrorId.c_binding_if_forbidden,
    @"
");

    Add(ErrorId.c_case_based_if_forbidden,
    @"
");

    Add(ErrorId.c_non_deterministic_loop_forbidden,
    @"
");

    Add(ErrorId.c_case_based_loop_forbidden,
    @"
");

    Add(ErrorId.c_no_assignments_to_seven_d_arrays,
    @"
");

    Add(ErrorId.c_bodyless_modify_statement_forbidden,
    @"
");

    Add(ErrorId.c_let_such_that_is_too_complex,
    @"
");

    Add(ErrorId.c_possibly_unsatisfied_postconditions,
    @"
");

    Add(ErrorId.c_stubbing_fields_not_recommended,
    @"
");

    Add(ErrorId.c_abstract_type_cannot_be_compiled_extern,
    @"
");

    Add(ErrorId.c_Go_unsupported_field,
    @"
");

    Add(ErrorId.c_Go_infeasible_conversion,
    @"
");
  }
}
