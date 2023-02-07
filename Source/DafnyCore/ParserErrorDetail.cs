// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Numerics;
using System.Globalization;
using static Microsoft.Dafny.ErrorDetail;

namespace Microsoft.Dafny;

public class ParserErrorDetail {

  public static void init() {

    ErrorDetail.Add(ErrorID.p_bad_const_initialize_op,
    @"
Dafny's syntax for initialization and assignment uses `:=`, not `=`.
In Dafny `=` is used only in type definitions.
"
    );

    ErrorDetail.Add(ErrorID.p_abstract_not_allowed,
    @"
Only modules may be declared abstract.
"
    );

    ErrorDetail.Add(ErrorID.p_no_ghost_for_by_method,
    @"
Functions with a [by method](../DafnyRef/DafnyRef#sec-function-declarations)
section to their body can be used both in ghost contexts and in non-ghost contexts; 
in ghost contexts the function body is used and in compiled contexts
the by-method body is used. The `ghost` keyword is not permitted on the
declaration.
"
    );

    ErrorDetail.Add(ErrorID.p_no_static,
    @"
Only some kinds of declarations can be declared 'static', most often
fields, constants, methods, and functions, and only within classes. 
Modules and the declarations within them are already always static.
"
    );

    ErrorDetail.Add(ErrorID.p_deprecated_semicolon,
  @"
Semicolons are required after statements and declarations in method bodies,  
but are deprecated after declarations within modules and types.
");

    ErrorDetail.Add(ErrorID.p_no_leading_underscore,
  @"
User-declared identifiers may not begin with an underscore;
such identifiers are reserved for internal use.
In match statements and expressions, an identifier
that is a single underscore is used as a wild-card match.
");

  }
}
