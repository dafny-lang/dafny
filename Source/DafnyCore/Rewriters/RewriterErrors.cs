using System.Collections.Generic;
using static Microsoft.Dafny.ErrorRegistry;

namespace Microsoft.Dafny;

public class RewriterErrors {

  public enum ErrorId {

    rw_timelimit_multiplier,
    rw_old_argument_not_on_heap,
    rw_induction_arguments_quantifier_mismatch,
    rw_induction_arguments_lemma_mismatch,
    rw_invalid_induction_attribute,
    rw_warn_constructor_parentheses,
    rw_unusual_indentation_start,
    rw_unusual_indentation_end,
  }
}