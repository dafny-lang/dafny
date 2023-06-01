// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

namespace Microsoft.Dafny;

public class GenericErrors {

  public enum ErrorId {
    g_cli_option_error,
    g_include_has_errors, // In Reporting.cs

    g_fuel_must_increase,
    g_no_old_unicode_char,
    g_unicode_escape_must_have_six_digits,
    g_unicode_escape_is_too_large,
    g_unicode_escape_may_not_be_surogate,
    g_U_unicode_chars_are_disallowed,
    g_deprecated_this_in_constructor_modifies_clause

  }
}