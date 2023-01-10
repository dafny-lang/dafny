// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Numerics;
using System.Globalization;

namespace Microsoft.Dafny;

public class ParserErrorDetail {

  public static string p_bad_const_initialize_op = "p_bad_const_initialize_op";
  public static string p_deprecated_semicolon = "p_deprecated_semicolon";
  public static string p_no_leading_underscore = "p_no_leading_underscore";
  public static string p_abstract_not_allowed = "p_abstract_not_allowed";
  public static string p_no_ghost_for_by_method = "p_no_ghost_for_by_method";
  public static string p_no_static = "p_no_static";
  public static void init() {

    ErrorDetail.Add(p_bad_const_initialize_op,
    @"
Dafny's syntax for initialization and assignment uses `:=`, not `=` (like some other languages).
In fact `=` is not used at all in Dafny.
"
    );

    ErrorDetail.Add(p_abstract_not_allowed,
    @"
Only modules may be declared abstract.
"
    );

    ErrorDetail.Add(p_no_ghost_for_by_method,
    @"
Functions with a [by method](../DafnyRef/DafnyRef#sec-function-declarations)
section to their body can be used both in ghost contexts and in non-ghost contexts; in ghost contexts the function body is used and in compiled contexts
the by-method body is used. The `ghost` keyword is not permitted on the
declaration.
"
    );

    ErrorDetail.Add(p_no_static,
    @"
Only some kinds of declarations can be declared 'static', most often
fields, constants, methods, and functions, and only within classes. 
Modules and the declarations within them are already always static.
"
    );

    ErrorDetail.Add(p_deprecated_semicolon,
  @"
Semicolons are required after statements and declarations in method bodies,  
but are deprecated after declarations within modules and types.
");

    ErrorDetail.Add(p_no_leading_underscore,
  @"
User-declared identifiers may not begin with an underscore;
such identifiers are reserved for internal use.
In match statements and expressions, an identifier
that is a single underscore is used as a wild-card match.
");

  }
}
