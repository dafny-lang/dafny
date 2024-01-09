using System.Collections.Generic;
using static Microsoft.Dafny.ErrorRegistry;

namespace Microsoft.Dafny;

public class RewriterErrors {

  public enum ErrorId {
    // ReSharper disable once InconsistentNaming
    rw_timelimit_multiplier,
    rw_old_argument_not_on_heap,
    rw_warn_negated_assertion,
    rw_induction_arguments_quantifier_mismatch,
    rw_induction_arguments_lemma_mismatch,
    rw_invalid_induction_attribute,
    rw_warn_constructor_parentheses,
    rw_unusual_indentation_start,
    rw_unusual_indentation_end,
    rw_test_methods_may_not_have_inputs,
    rw_test_method_has_too_many_returns,
    rw_clause_cannot_be_compiled,
    rw_no_wrapper,
    rw_unreachable_by_test,
    rw_print_attribute_forbidden_on_functions,
    rw_print_attribute_forbidden_on_ghost_methods,
    rw_override_must_preserve_printing,
    rw_print_attribute_takes_no_arguments,
    rw_no_print_in_function_by_method,
    rw_print_attribute_required_to_print,
    rw_function_by_method_may_not_call_printing_method,
    rw_must_be_print_to_call_printing_method,
  }
}