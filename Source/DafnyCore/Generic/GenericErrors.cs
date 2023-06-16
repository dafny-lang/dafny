// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

namespace Microsoft.Dafny;
using static Microsoft.Dafny.ErrorRegistry;

public class GenericErrors {

  public enum ErrorId {
    g_deprecated_this_in_constructor_modifies_clause,
    g_no_old_unicode_char,
    g_unicode_escape_must_have_six_digits,
    g_unicode_escape_is_too_large,
    g_unicode_escape_may_not_be_surrogate,
    g_U_unicode_chars_are_disallowed,
    g_option_error,
    g_feature_unsupported,
    g_fuel_must_increase,

  }

  static GenericErrors() {

    Add(ErrorId.g_deprecated_this_in_constructor_modifies_clause,
     @"
The purpose of a constructor is to initialize a newly allocated instance of a class.
Hence it always modifies the `this` object.
Previously it was required to list `this` in the modifies clause of the
constructor to specify this property, but now `this` is always implicitly 
a part of the modifies clause. 
If the constructor only modifies its own object (as is the very common case)
then no explicit modifies clause is needed at all.
"); // TODO _ add a quick fix to remove the this, or maybe the whole clause

  }
}