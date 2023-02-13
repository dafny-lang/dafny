// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;

namespace Microsoft.Dafny;
public static class ErrorDetail {

  public enum ErrorID {
    None,

    p_duplicate_modifier,
    p_abstract_not_allowed,
    p_no_ghost_for_by_method,
    p_ghost_forbidden_default,
    p_ghost_forbidden,
    p_no_static,
    p_deprecated_attribute,
    p_literal_string_required,
    p_no_leading_underscore,
    p_bitvector_too_large,
    p_array_dimension_too_large,
    p_superfluous_export,
    p_bad_module_decl,
    p_extraneous_comma_in_export,
    p_top_level_field,
    p_bad_datatype_refinement,
    p_no_mutable_fields_in_value_types,
    p_bad_const_initialize_op,
    p_const_is_missing_type_or_init,
    p_misplaced_ellipsis_in_newtype,
    p_output_of_function_not_ghost,
    p_ghost_function_output_not_ghost,
    p_no_new_on_output_formals,
    p_no_nameonly_on_output_formals,
    p_no_older_on_output_formals,
    p_var_decl_must_have_type,
    p_no_init_for_var_field,
    p_datatype_formal_is_not_id,
    p_nameonly_must_have_parameter_name,
    p_should_be_yields_instead_of_returns,
    p_type_parameter_variance_forbidden,
    p_unexpected_type_characteristic,
    p_missing_type_characteristic,
    p_illegal_type_characteristic,
    p_deprecated_colemma,
    p_deprecated_inductive_lemma,
    p_constructor_not_in_class,
    p_method_missing_name,
    p_extraneous_k,
    p_constructors_have_no_out_parameters,
    p_reads_star_must_be_alone,
    p_no_defaults_for_out_parameters,
    p_set_only_one_type_parameter,
    p_iset_only_one_type_parameter,
    p_multiset_only_one_type_parameter,
    p_seq_only_one_type_parameter,
    p_map_needs_two_type_parameters,
    p_imap_needs_two_type_parameters,



    p_deprecating_function_method,
    p_deprecated_semicolon,
    sc_malformed_pragma,
    sc_unknown_pragma,
  }

  // This dictionary maps an errorID (error code) to a code action and explanatory text
  // (which could be moderately lengthy)


  static private Dictionary<ErrorID, string> errorDetailMap = new Dictionary<ErrorID, string>();

  static ErrorDetail() { init(); }

  static bool initialized = false;
  public static void init() {
    if (!initialized) {
      ParserErrorDetail.init();
      initialized = true;
    }
  }
  // Adds information into the dictionary
  public static void Add(ErrorID errorID, string detail) {
    errorDetailMap.Add(errorID, detail);
  }

  // Returns the error detail for the given error ID;
  // result could be null if there is no such detail
#nullable enable
  public static string? GetDetail(ErrorID errorID) {
    if (errorDetailMap.TryGetValue(errorID, out var result)) {
      return result;
    }
    return null;
  }
#nullable disable
}


