// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Numerics;
using System.Globalization;
using static Microsoft.Dafny.ErrorDetail;

namespace Microsoft.Dafny;

public class ParserErrorDetail {

  public static void init() {

    Add(ErrorID.p_duplicate_modifier,
    @"
No Dafny modifier, such as [`abstract`, `static`, `ghost`](../DafnyRef/DafnyRef#sec-declaration-modifiers) may be repeated
Such repetition would be superfluous even if allowed.
");

    Add(ErrorID.p_abstract_not_allowed,
    @"
Only modules may be declared abstract.
"
    );

    Add(ErrorID.p_no_ghost_for_by_method,
    @"
Functions with a [by method](../DafnyRef/DafnyRef#sec-function-declarations)
section to their body can be used both in ghost contexts and in non-ghost contexts; 
in ghost contexts the function body is used and in compiled contexts
the by-method body is used. The `ghost` keyword is not permitted on the
declaration.
"
    );

    Add(ErrorID.p_ghost_forbidden_default,
    @"
For versions prior to Dafny 4, the `function` keyword meant a ghost function
and `function method` meant a non-ghost function. 
From Dafny 4 on, `ghost function` means a ghost function and 
`function` means a non-ghost function. 
See the discussion [here](../DafnyRef/DafnyRef#sec-function-syntax) for
a discussion of options to control this feature.
");

    Add(ErrorID.p_ghost_forbidden,
    @"
Only some kinds of declarations can be declared `ghost`, most often functions,
fields, and local declarations. In the example, a `module` may not be `ghost`.
");

    Add(ErrorID.p_no_static,
    @"
Only some kinds of declarations can be declared 'static', most often
fields, constants, methods, and functions, and only within classes. 
Modules and the declarations within them are already always static.
");

    ErrorDetail.Add(ErrorID.p_deprecated_attribute,
    @"
The `{:handle}` and `{:dllimport}` attributes are obsolete and unmaintained. They will be removed.
");

    Add(ErrorID.p_literal_string_required,
    @"
The value of an options attribute cannot be a computed expression. It must be a literal string.
");

    Add(ErrorID.p_no_leading_underscore,
  @"
User-declared identifiers may not begin with an underscore;
such identifiers are reserved for internal use.
In match statements and expressions, an identifier
that is a single underscore is used as a wild-card match.
");

    Add(ErrorID.p_bitvector_too_large,
    @"
A bitvector type name is the characters 'bv' followed by a non-negative
integer literal. However, dafny only supports widths up to the largest
signed 32-bit integer (2147483647).
");

    Add(ErrorID.p_array_dimension_too_large,
    @"
A multi-dimensional array type name is the characters 'array' followed by
a positive integer literal. However, dafny only supports numbers of 
dimensions up to the largest signed 32-bit integer (2147483647).
In practice (as of v3.9.1) dimensions of more than a few can take 
overly long to resolve ([Issue #3180](https://github.com/dafny-lang/dafny/issues/3180)).
");

    Add(ErrorID.p_superfluous_export,
@"
Although all top-level declarations are contained in an implicit top-level module, there is no syntax to import that module.
Such an import would likely cause a circular module dependency error.
If the implicit module cannot be imported, there is no point to any export declarations inside the implicit module.
");

    Add(ErrorID.p_bad_module_decl,
    @"
The [syntax for a module declaration](../DafnyRef/DafnyRef#sec-modules) is either `module M { ... }` or
`module M refines N { ... }` with optional attributes after the `module` keyword.
This error message often occurs if the `refines` keyword is misspelled.
   ");

    Add(ErrorID.p_extraneous_comma_in_export,
    @"
An export declaration consists of one or more `reveals`, `provides`, and extends clauses. Each clause contains
a comma-separated list of identifiers, but the clauses themselves are not separated by any delimiter.
So in the example above, the comma after `a` is wrong in each export declaration. 
This mistake is easy to make when the clauses are on the same line.
");

    Add(ErrorID.p_top_level_field,
    @"
`var` declarations are used to declare mutable fields of classes, local variables in method bodies, and identifiers in let-expressions.
But mutable field declarations are not permitted at the static module level, including in the (implicit) toplevel module.
Rather, you may want the declaration to be a `const` declaration or you may want the mutable field to be declared in the body of a class.
");

    Add(ErrorID.p_bad_datatype_refinement,
    @"
There are limitations on refining a datatype, namely that the set of constructors cannot be changed.
It is only allowed to add members to the body of the datatype.
");


    ErrorDetail.Add(ErrorID.p_bad_const_initialize_op,
    @"
Dafny's syntax for initialization and assignment uses `:=`, not `=`.
In Dafny `=` is used only in type definitions.
");

    ErrorDetail.Add(ErrorID.p_deprecated_semicolon,
    @"
Semicolons are required after statements and declarations in method bodies,  
but are deprecated after declarations within modules and types.
");


  }
}
