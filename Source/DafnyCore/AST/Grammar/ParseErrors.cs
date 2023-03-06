// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System.Collections.Generic;
using static Microsoft.Dafny.ErrorRegistry;

namespace Microsoft.Dafny;

public class ParseErrors {

  public enum ErrorId {
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
    sc_malformed_pragma, // TODO no description is provided
    sc_unknown_pragma, // TODO no description is provided
  }

  static ParseErrors() {

    Add(ErrorId.p_duplicate_modifier,
    @"
No Dafny modifier, such as [`abstract`, `static`, `ghost`](https://dafny.org/latest/DafnyRef/DafnyRef#sec-declaration-modifiers) may be repeated
Such repetition would be superfluous even if allowed.
", Remove(true, "remove duplicate modifier"));

    Add(ErrorId.p_abstract_not_allowed,
    @"
Only modules may be declared abstract.
", Remove(true));

    Add(ErrorId.p_no_ghost_for_by_method,
    @"
Functions with a [by method](https://dafny.org/latest/DafnyRef/DafnyRef#sec-function-declarations)
section to their body can be used both in ghost contexts and in non-ghost contexts; 
in ghost contexts the function body is used and in compiled contexts
the by-method body is used. The `ghost` keyword is not permitted on the
declaration.
", Remove(true));

    Add(ErrorId.p_ghost_forbidden_default,
    @"
For versions prior to Dafny 4, the `function` keyword meant a ghost function
and `function method` meant a non-ghost function. 
From Dafny 4 on, `ghost function` means a ghost function and 
`function` means a non-ghost function. 
See the discussion [here](https://dafny.org/latest/DafnyRef/DafnyRef#sec-function-syntax) for
a discussion of options to control this feature.
", Remove(true));

    Add(ErrorId.p_ghost_forbidden,
    @"
Only some kinds of declarations can be declared `ghost`, most often functions,
fields, and local declarations. In the example, a `module` may not be `ghost`.
", Remove(true));

    Add(ErrorId.p_no_static,
    @"
Only some kinds of declarations can be declared 'static', most often
fields, constants, methods, and functions, and only within classes. 
Modules and the declarations within them are already always static.
", Remove(true));

    Add(ErrorId.p_deprecated_attribute,
    @"
The `{:handle}` and `{:dllimport}` attributes are obsolete and unmaintained. They will be removed.
", Remove(true, "remove attribute")); // TODO test!!

    Add(ErrorId.p_literal_string_required,
    @"
The value of an options attribute cannot be a computed expression. It must be a literal string.
", Replace("\"\"", "replace with empty string"));

    Add(ErrorId.p_no_leading_underscore,
  @"
User-declared identifiers may not begin with an underscore;
such identifiers are reserved for internal use.
In match statements and expressions, an identifier
that is a single underscore is used as a wild-card match.
", range => new List<DafnyAction> { new("remove underscore", 
    new [] {
      new DafnyCodeActionEdit(range, range.PrintOriginal().Substring(1))
    })
  });

    Add(ErrorId.p_bitvector_too_large,
    @"
A bitvector type name is the characters 'bv' followed by a non-negative
integer literal. However, dafny only supports widths up to the largest
signed 32-bit integer (2147483647).
");

    Add(ErrorId.p_array_dimension_too_large,
    @"
A multi-dimensional array type name is the characters 'array' followed by
a positive integer literal. However, dafny only supports numbers of 
dimensions up to the largest signed 32-bit integer (2147483647).
In practice (as of v3.9.1) dimensions of more than a few can take 
overly long to resolve ([Issue #3180](https://github.com/dafny-lang/dafny/issues/3180)).
");

    Add(ErrorId.p_superfluous_export,
@"
Although all top-level declarations are contained in an implicit top-level module, there is no syntax to import that module.
Such an import would likely cause a circular module dependency error.
If the implicit module cannot be imported, there is no point to any export declarations inside the implicit module.
"); // TODO add a code action

    Add(ErrorId.p_bad_module_decl,
    @"
The [syntax for a module declaration](https://dafny.org/latest/DafnyRef/DafnyRef#sec-modules) is either `module M { ... }` or
`module M refines N { ... }` with optional attributes after the `module` keyword.
This error message often occurs if the `refines` keyword is misspelled.
   ");

    Add(ErrorId.p_extraneous_comma_in_export,
    @"
An export declaration consists of one or more `reveals`, `provides`, and extends clauses. Each clause contains
a comma-separated list of identifiers, but the clauses themselves are not separated by any delimiter.
So in the example above, the comma after `a` is wrong in each export declaration. 
This mistake is easy to make when the clauses are on the same line.
", Remove(false, "remove comma"));

    Add(ErrorId.p_top_level_field,
    @"
`var` declarations are used to declare mutable fields of classes, local variables in method bodies, and identifiers in let-expressions.
But mutable field declarations are not permitted at the static module level, including in the (implicit) toplevel module.
Rather, you may want the declaration to be a `const` declaration or you may want the mutable field to be declared in the body of a class.
", Replace("const", "replace 'var' by 'const'"));

    Add(ErrorId.p_bad_datatype_refinement, // TODO errorId is never used in parser
    @"
There are limitations on refining a datatype, namely that the set of constructors cannot be changed.
It is only allowed to add members to the body of the datatype.
");

    Add(ErrorId.p_no_mutable_fields_in_value_types,
    @"
The `var` declaration declares a mutable field, which is only permitted within
classes, traits and iterators. 
`const` declarations can be members of value-types, such as datatypes.
", Replace("const"));

    Add(ErrorId.p_bad_const_initialize_op,
    @"
Dafny's syntax for initialization and assignment uses `:=`, not `=`.
In Dafny, `=` is used only in type definitions.
", Replace(":="));

    Add(ErrorId.p_const_is_missing_type_or_init,
    @"
A `const` declaration needs its type indicated by either an explicit type
or a right-hand-side expression, whose type is then the type of the 
declared identifier. 
So use syntax either like `const i: int` or `const i:= 5` (or both together).
", Insert(": int := 42", "add example"));

    Add(ErrorId.p_misplaced_ellipsis_in_newtype,
    @"
There are limitations on refining a newtype, namely that the base type cannot be changed. You can change an opaque type into a newtype, however.
");

    Add(ErrorId.p_output_of_function_not_ghost,
    @"
The output of a predicate or function cannot be ghost.
It is implicitly ghost if the function is ghost itself.
", Remove(true));

    Add(ErrorId.p_ghost_function_output_not_ghost, // TODO errorId is never used in parser
    @"
If a method, function, or predicate is declared as ghost, then its formal parameters may not also be declared ghost.
Any use of this construct will always be in ghost contexts.
", Remove(true));

    Add(ErrorId.p_no_new_on_output_formals, // TODO errorId is never used in parser
    @"
The `new` modifier only applies to input parameters.
", Remove(true));

    Add(ErrorId.p_no_nameonly_on_output_formals, // TODO errorId is never used in parser
    @"
The `nameonly` modifier only applies to input parameters.
", Remove(true));

    Add(ErrorId.p_no_older_on_output_formals, // TODO errorId is never used in parser
    @"
The `older` modifier only applies to input parameters.
", Remove(true));

    Add(ErrorId.p_var_decl_must_have_type,
    @"
Because a mutable field does not have initializer, it must have a type (as in `var f: int`).
`const` declarations may have initializers; if they do they do not need an explicit type.
");

    Add(ErrorId.p_no_init_for_var_field,
    @"
Dafny does not allow field declarations to have initializers. They are initialized in constructors.
Local variable declarations (which also begin with `var`) may have initializers.
");

    Add(ErrorId.p_datatype_formal_is_not_id,
    @"
Datatype constructors can have formal parameters, declared with the usual syntax: 'name: type'.
In datatype constructors the 'name :' is optional; one can just state the type.
However, if there is a name, it may not be a typename, as in the failing example above.
The formal parameter name should be a simple identifier that is not a reserved word.
");

    Add(ErrorId.p_nameonly_must_have_parameter_name,
    @"
The parameters of a datatype constructor do not need to have names -- it is allowed to just give the type.
However, if `nameonly` is used, meaning the constructor can be called using named parameters,
then the name must be given, as in `datatype D = D (i: int, nameonly j: int) {}`

More detail is given [here](https://dafny.org/latest/DafnyRef/DafnyRef#sec-parameter-bindings).
", Remove(true));

    Add(ErrorId.p_should_be_yields_instead_of_returns,
    @"
An [iterator](https://dafny.org/latest/DafnyRef/DafnyRef#sec-iterator-types) is like a co-routine: 
its control flow produces (yields) a value, but the execution continues from that point (a yield statement) to go on to produce the next value, rather than exiting the method. 
To accentuate this difference, a `yield` statement is used to say when the next value of the iterator is ready, rather than a `return` statement.
In addition, the declaration does not use `returns` to state the out-parameter, as a method would. Rather it has a `yields` clause.
The example above is a valid example if `returns` is replaced by `yields`.
", Replace("yields"));

    Add(ErrorId.p_type_parameter_variance_forbidden,
    @"
[Type-parameter variance](https://dafny.org/latest/DafnyRef/DafnyRef#sec-type-parameter-variance) is specified by a 
`+`, `-`, `*` or `!` before the type-parameter name.
Such designations are allowed in generic type declarations but not in generic method, function, or predicate declarations.
", Remove(false, "remove type parameter variance"));

    Add(ErrorId.p_unexpected_type_characteristic,
    @"
[Type characteristics](https://dafny.org/latest/DafnyRef/DafnyRef#sec-type-parameters), 
indicated in parentheses after the type name, state properties of the otherwise uninterpreted or opaque type.
The currently defined type characteristics are designated by `==` (equality-supporting), `0` (auto-initializable), `00` (non-empty), and `!new` (non-reference).
", Replacements(new[] {
      ("==", "replace with '==' - this type supports equality"),
      ("0", "replace with '0' - this type is auto-initializable"),
      ("00", "replace with '00' - this type is nonempty"),
      ("!new", "replace with '!new' - this type is not allocated on the heap")
    }));

    Add(ErrorId.p_missing_type_characteristic,
    @"
[Type characteristics](https://dafny.org/latest/DafnyRef/DafnyRef#sec-type-parameters), 
state properties of the otherwise uninterpreted or opaque type.
They are given in a parentheses-enclosed, comma-separated list after the type name.
The currently defined type characteristics are designated by `==` (equality - supporting), `0` (auto - initializable), `00` (non - empty), and `!new` (non - reference).
");

    Add(ErrorId.p_illegal_type_characteristic,
    @"
[Type characteristics](https://dafny.org/latest/DafnyRef/DafnyRef#sec-type-parameters), 
indicated in parentheses after the type name, state properties of the otherwise uninterpreted or opaque type.
The currently defined type characteristics are designated by `==` (equality - supporting), `0` (auto - initializable), `00` (non - empty), and `!new` (non - reference).
Type parameters are given in a parentheses-enclosed, comma-separated list after the type name.
");

    Add(ErrorId.p_deprecated_colemma,
    @"
The adjectives `least` and `greatest` for lemmas and functions are more consistent with the nomenclature for coinduction.
", Replace("greatest lemma"));

    Add(ErrorId.p_deprecated_inductive_lemma,
  @"
The adjectives `least` and `greatest` for lemmas and functions are more consistent with the nomenclature for coinduction.
", Replace("least"));

    Add(ErrorId.p_constructor_not_in_class,
    @"
Constructors are methods that initialize class instances. That is, when a new instance of a class is being created, 
using the `new` object syntax, some constructor of the class is called, perhaps a default anonymous one.
So, constructor declarations only make sense within classes.
", Replace("method"));

    Add(ErrorId.p_method_missing_name,
    @"
A method declaration always requires an identifier between the `method` keyword and the `(` that starts the formal parameter list.
This is the case even when, as in the example above, a name is specified using `:extern`. The extern name is only used in the
compiled code; it is not the name used to refer to the method in Dafny code
");

    Add(ErrorId.p_extraneous_k,
    @"
Least and greatest lemmas and predicates have a special parameter named `k`.
Its type is specified in square brackets between the lemma/predicate name and the rest of the signature.
The type may be either `nat` or `ORDINAL`.
But this type is specified only for `least` and `greatest` constructs.
", Remove(false));

    Add(ErrorId.p_constructors_have_no_out_parameters, // TODO errorId is never used in parser
    @"
Constructors are used to initalize the state of an instance of a class.
Thus they typically set the values of the fields of the class instance.
Constructors are used in `new` object expressions, which return 
a reference to the newly constructed object (as in `new C(42)`).
There is no syntax to receive out-parameter values of a constructor
and they may not be declared. 
(This is similar to constructors in other programming languages, like Java.)
");

    Add(ErrorId.p_reads_star_must_be_alone,
    @"
A reads clause lists the objects whose fields the function is allowed to read (or expressions 
containing such objects). `reads *` means the function may read anything.
So it does not make sense to list `*` along with something more specific.
If you mean that the function should be able to read anything, just list `*`.
Otherwise, omit the `*` and list expressions containing all the objects that are read.
");

    Add(ErrorId.p_no_defaults_for_out_parameters,
    @"
Out-parameters of a method are declared (inside the parentheses after the `returns` keyword)
with just an identifier and a type, separated by a colon. 
No initializing value may be given. If a default value is needed, assign the out-parameter
that value as a first statement in the body of the method.
", Remove(false, "remove initializer"));

    Add(ErrorId.p_set_only_one_type_parameter,
    @"
A `set` type has one type parameter, namely the type of the elements of the set.
The error message states that the parser sees some number of type parameters different than one.
The type parameters are listed in a comma-separated list between `<` and `>`, after the type name.
");

    Add(ErrorId.p_iset_only_one_type_parameter,
    @"
A `iset` type has one type parameter, namely the type of the elements of the set.
The error message states that the parser sees some number of type parameters different than one.
The type parameters are listed in a comma-separated list between `<` and `>`, after the type name.
");

    Add(ErrorId.p_multiset_only_one_type_parameter,
    @"
A `multiset` type has one type parameter, namely the type of the elements of the multiset.
The error message states that the parser sees some number of type parameters different than one.
The type parameters are listed in a comma-separated list between `<` and `>`, after the type name.
");

    Add(ErrorId.p_seq_only_one_type_parameter,
    @"
A `seq` type has one type parameter, namely the type of the elements of the sequence.
The error message states that the parser sees some number of type parameters different than one.
The type parameters are listed in a comma-separated list between `<` and `>`, after the type name.
");

    Add(ErrorId.p_map_needs_two_type_parameters,
    @"
A `map` type has two type parameters: the type of the keys and the type of the values.
The error message states that the parser sees some number of type parameters different than two.
");

    Add(ErrorId.p_imap_needs_two_type_parameters,
    @"
A `imap` type has two type parameters: the type of the keys and the type of the values.
The error message states that the parser sees some number of type parameters different than two.
");

    Add(ErrorId.p_deprecating_function_method, // TODO errorId is never used in parser
    @"
In Dafny 4 on, the phrases `function method` and `predicate method` are no
longer accepted. Use `function` for compiled, non-ghost functions and
`ghost function` for non-compiled, ghost functions, and similarly for predicates.
See [the documentation here](https://dafny.org/latest/DafnyRef/DafnyRef#sec-function-syntax).
");

    Add(ErrorId.p_deprecated_semicolon,
    @"
Semicolons are required after statements and declarations in method bodies,  
but are deprecated after declarations within modules and types.
");
  }
}
