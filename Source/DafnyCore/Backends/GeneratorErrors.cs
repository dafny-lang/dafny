// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System.Collections.Generic;
using static Microsoft.Dafny.ErrorRegistry;

namespace Microsoft.Dafny;

public class GeneratorErrors {

  public enum ErrorId {
    None,
    c_process_exit,
    c_process_failed_to_start,
    c_unsupported_feature,
    c_abstract_type_cannot_be_compiled,
    c_iterators_are_not_deterministic,
    c_iterator_has_no_body,
    c_constructorless_class_forbidden,
    c_method_may_not_be_main_method,
    c_could_not_find_stipulated_main_method,
    c_more_than_one_explicit_main_method,
    c_method_not_permitted_as_main,
    c_more_than_one_default_Main_method,
    c_Main_method_not_permitted,
    c_function_has_no_body,
    c_test_function_must_be_compilable,
    c_invalid_synthesize_method,
    c_method_has_no_body,
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

    f_unsupported_feature,

  }

  static GeneratorErrors() {

    Add(ErrorId.c_process_exit,
    @"
The dafny compiler prepares a representation of the Dafny program in the desired target programming
language and then invokes the target language's compiler on those files as a subsidiary process.
This error message indicates that the sub-process terminated with an error of some sort.
This should not ordinarily happen. Some possible causes are
- lack of resources that caused the underlying compiler to fail
- lack of or corrupted installation of the underlying compiler
- a bug in dafny whereby the source code it prepares for the compiler is faulty

There may be additional error messages from the underlying compiler that can help debug this situation.
You can also attempt to run the target programming language compiler manually in your system 
to make sure it is functional.
".TrimStart());

    Add(ErrorId.c_process_failed_to_start,
    @"
The dafny compiler prepares a representation of the Dafny program in the desired target programming
language and then invokes the target language's compiler on those files as a subsidiary process.
This error message indicates that this sub-process would not start;
it gives some additional information about what the invoking process was told about the failure to start.

Typically this error happens when the installation of the underlying compiler is not present or is incomplete,
such as the proper files not having the correct permissions.
".TrimStart());

    Add(ErrorId.c_unsupported_feature,
    @"
This messages indicates two problems:
- the given feature is not supported in the compiler for the target language but is present in the program,
so the program will need to be revised to avoid this feature;
- the feature is not listed in the in-tool list of unsupported features.
The latter is an omission in the in-tool documentation. Please report this error message and the part of the
program provoking it to the Dafny team's [issue tracker](https://github.com/dafny-lang/dafny/issues).
".TrimStart());

    Add(ErrorId.c_abstract_type_cannot_be_compiled,
    @"
[Abstract types](../DafnyRef/DafnyRef#sec-abstract-types) are declared like `type T`.
They can be useful in programs where the particular characteristics of the type
do not matter, such as in manipulating generic collections.
Such programs can be verified, but in order to be compiled to something executable, 
the type must be given an actual definition. 
If the definition really does not matter, just give it a definition like 
`type T = bool` or `type T = `int`.

Note that some properties of a type an be indicated using a [type characteristic](../DafnyRef/DafnyRef#sec-type-characteristics).
For example, [`type T(00)` indicates that the type `T` is non-empty](../DafnyRef/DafnyRef#sec-nonempty-types).
".TrimStart());

    Add(ErrorId.c_iterators_are_not_deterministic,
    @"
The `--enforce-determinism` option requires a target program to be deterministic and predictable:
there may be no program statements that have an arbitrary, even if deterministic, result.
In an iterator, the yield parameters are initialized with arbitary values and can be read before 
they are set with actual values, so there is a bit of nondeterminism.
Consequently, iterators in general are not permitted along with `--enforce-determinism`.
".TrimStart());

    Add(ErrorId.c_iterator_has_no_body,
    @"
Programs containing iterators without bodies can be verified.
However, a body-less iterator is an unchecked assumption (even if it is ghost).
Consequently, like body-less functions and loops, dafny will not
compile a program containing an iterator without a body.
Furthermore, if the iterator is non-ghost, it cannot be compiled if it does not have a body.
".TrimStart());

    Add(ErrorId.c_constructorless_class_forbidden,
    @"
The `--enforce-determinism` option prohibits all non-deterministic operations in a Dafny program.
One of these operations is the arbitrary values assigned to non-explicitly-initialized fields in a default constructor.
Consequently an explicit constructor is required.
".TrimStart());

    Add(ErrorId.c_method_may_not_be_main_method,
    @"
To create an executable program, the compiler needs to know which is the method 
to call to start the program, typically known as the 'main' method or main entry point. 
`dafny` chooses such a method based on a few rules (cf. [details in the Dafny User Guide](#sec-user-guide-main)).

But there are restrictions on which methods may be used as a main entry point.
Most importantly
- the method must take no input arguments or just one argument of type `seq<string>`
- it must not be ghost
- the method may be a class method, but then typically it is `static`

Most commonly and for clarity, the intended main method is marked with the attribute `{:main}`.
".TrimStart());

    Add(ErrorId.c_could_not_find_stipulated_main_method,
    @"
In the legacy command-line syntax, the main method may be specified on the command-line.
When doing so, the name given must be a fully-qualified name.
For instance. a method `m` in a (top-level) module `M` is named `M.m` 
or in a class `C` in a module `M` is named `M.C.m`.
This error message indicates that dafny does not recognize the name given as the name of a method.
".TrimStart());

    Add(ErrorId.c_more_than_one_explicit_main_method,
    @"
When searching all the files in the program (including `include`d ones), dafny found more than one method marked
with `{:main}`. The error location is that of one of the methods and the error refers to another.
The tool does not know which one to use. 
The solution is to remove the `{:main}` attribute from all but one.

Note that entry points that are intended as unit tests can be marked with `{:test}` instead.
".TrimStart());

    Add(ErrorId.c_method_not_permitted_as_main,
    @"
Only some methods may be used as entry points and the one indicated may not.
The principal restrictions are these ([more details in the Dafny User Guide](#sec-user-guide-main)):
- the method must take no input arguments or just one argument of type `seq<string>`
- it must not be ghost
- the method may be a class method, but then typically it is `static`
".TrimStart());

    Add(ErrorId.c_more_than_one_default_Main_method,
    @"
In the absence of any `{:main}` attributes, dafny chooses a method named `Main` as the main entry point.
When searching all the files in the program (including `include`d ones), dafny found more than one method named `Main`.
The error location is that of one of the methods and the error text refers to another.
The solution is to mark one of them as `{:main}`.

Note that entry points that are intended as unit tests can be marked with `{:test}` instead.
".TrimStart());

    Add(ErrorId.c_Main_method_not_permitted,
    @"
If dafny finds no methods marked `{:main}`, it then looks for a method named `Main`
to use as the starting point for the program.
This error occurs if the `Main` method that is found
does not qualify as a main entry point because it violates one or more of the [rules](#sec-user-guide-main),
as given by the reason in the error message.
".TrimStart());

    Add(ErrorId.c_function_has_no_body,
    @"
The given function has no body, which is OK for verification, but not OK for compilation 
--- the compiler does not know what content to give it.
Even ghost functions must have bodies because body-less ghost functions are a form of unchecked assumptions.
".TrimStart());

    Add(ErrorId.c_test_function_must_be_compilable,
    @"
Only compiled functions and methods may be tested using the `dafny test` command, 
which tests everything marked with `{:test}`.
However this function is a ghost function, and consequently cannot be tested during execution.
If you want the function to be compiled,
declare the function as a `function` instead of `ghost function` in Dafny 4 
or as `function method` instead of `function` in Dafny 3.
".TrimStart());

    Add(ErrorId.c_invalid_synthesize_method,
    @"
The `{:synthesize}` attribute is an experimental attribute used to create 
a mock object for methods that do not have bodies.
It is currently only available for compiling to C# and in conjunction with the Moq library.
See the [reference manual section on {:synthesize}](../DafnyRef/DafnyRef#sec-synthesize-attr) for more detail.
".TrimStart());

    Add(ErrorId.c_method_has_no_body,
    @"
To be part of a compiled program, each method must have a body.
Ghost methods are the equivalent of unchecked assumptions
so they too must have bodies.
".TrimStart());

    Add(ErrorId.c_forall_statement_has_no_body,
    @"
A method may be parsed and verified even if a [forall statement](../DafnyRef/DafnyRef#sec-forall-statement) is missing a body. 
However, the body must be supplied before the program can be compiled,
even if the method is `ghost`. Body-less foralls in ghost methods are 
unchecked assumptions.
".TrimStart());

    Add(ErrorId.c_loop_has_no_body,
    @"
A method may be parsed and verified even if a loop is missing a body. 
Note that a missing body is different than an empty body, which is just `{ }`.
However, the body must be supplied before the program can be compiled,
even if the method is `ghost`. 
Body-less loops in ghost methods are similar to unchecked assumptions.
".TrimStart());

    Add(ErrorId.c_nondeterminism_forbidden,
    @"
The `--enforce-determinism` option requires a target program to be deterministic and predictable:
there may be no program statements that have an arbitrary, even if deterministic, result.
Hence this 'assign any legal value' (`... := *`) statement is not permitted with `--enforce-determinism`.

There are a few different forms of this kind of assignment:
- `x := *;`
- `x, y, z := 3, *, 42;`
- `forall i | 0 <= i < a.Length { a[i] := *; }`
".TrimStart());

    Add(ErrorId.c_assign_such_that_forbidden,
    @"
The `--enforce-determinism` option requires a target program to be deterministic and predictable:
there may be no program statements that have an arbitrary, even if deterministic, result.
Hence this 'assign any value that satisfies the predicate' (`:|`) statement is not permitted with `--enforce-determinism`,
even if there is only one such possible value.
(The tool does not try to determine whether there is just one value and
whether there is a reasonable way to compute the value.)
".TrimStart());

    Add(ErrorId.c_assign_such_that_is_too_complex,
    @"
To compile an assign-such-that statement, Dafny needs to find some appropriate bounds for each variable.
However, in this case the expression is too complex for Dafny's heuristics.
".TrimStart());

    Add(ErrorId.c_nondeterministic_if_forbidden,
    @"
The `--enforce-determinism` option requires a target program to be deterministic and predictable:
there may be no program statements that have an arbitrary, even if deterministic, result.
Hence this 'non-deterministic if' (`if *`) statement is not permitted with `--enforce-determinism`.
".TrimStart());

    Add(ErrorId.c_binding_if_forbidden,
    @"
The `--enforce-determinism` option requires a target program to be deterministic and predictable:
there may be no program statements that have an arbitrary, even if deterministic, result.
The [`if` with a binding guard](../DafnyRef/DafnyRef#sec-binding-guards) (`if ... :| `) checks that the 
given predicate is satisfiable by some value. If not, then the 'else' branch is executed;
but if so, the 'then' branch is executed with an arbitrary value that satisifies the predicate.
Because of this arbitrary selection, the if-with-binding-guard is not permitted with `--enforce-determinism`,
even if there is exactly one value that satisfies the predicate.
(The tool does not try to determine whether there is just one value or
whether there is a reasonable way to compute a value.)
".TrimStart());

    Add(ErrorId.c_case_based_if_forbidden,
    @"
The `--enforce-determinism` option requires a target program to be deterministic and predictable:
there may be no program statements that have an arbitrary, even if deterministic, result.
The case-based if statement allows the case guards to be evaluated in an arbitrary order and
an arbitrary one of those found to be true is chosen to be executed.
Hence the case-based if is not permitted with `--enforce-determinism`.

To enforce a deterministic order to the evaluation, use a chain of if-then-else statements.
".TrimStart());

    Add(ErrorId.c_non_deterministic_loop_forbidden,
    @"
The `--enforce-determinism` option requires a target program to be deterministic and predictable:
there may be no program statements that have an arbitrary, even if deterministic, result.
Hence this 'non-deterministic while' (`while *`) statement is not permitted with `--enforce-determinism`.
".TrimStart());

    Add(ErrorId.c_case_based_loop_forbidden,
    @"
The `--enforce-determinism` option requires a target program to be deterministic and predictable:
there may be no program statements that have an arbitrary, even if deterministic, result.
The case-based while statement allows the case guards to be evaluated in an arbitrary order and
an arbitrary one of those found to be true is chosen to be executed.
Hence the case-based loop is not permitted with `--enforce-determinism`.

To enforce a deterministic order to the evaluation, use a chain of if-then-else statements
or series of `if` statements in which the then-branch ends in a continue statement.
".TrimStart());

    Add(ErrorId.c_no_assignments_to_seven_d_arrays,
    @"
_The documentation of this problem is in progress._
".TrimStart());

    Add(ErrorId.c_bodyless_modify_statement_forbidden,
    @"
The `--enforce-determinism` option requires a target program to be deterministic and predictable:
there may be no program statements that have an arbitrary, even if deterministic, result.

The [`modify` statement](../DafnyRef/DafnyRef#sec-modify-statement) allows the program to modify 
the state of the given objects in an arbitrary way
(though each field still has a legal value of its declared type).
Hence such a statement is not permitted with `--enforce-determinism`.

Note that a `modify` statement with a body is deprecated.
".TrimStart());

    Add(ErrorId.c_let_such_that_is_too_complex,
    @"
_The documentation of this problem is in progress._
".TrimStart());

    Add(ErrorId.c_possibly_unsatisfied_postconditions,
    @"
This message relates to mocking methods in C# with the Moq framework. 
See the [reference manual section on {:synthesize}](../DafnyRef/DafnyRef#sec-synthesize-attr) for more detail.
".TrimStart());

    Add(ErrorId.c_stubbing_fields_not_recommended,
    @"
This message relates to mocking methods in C# with the Moq framework. 
See the [reference manual section on {:synthesize}](../DafnyRef/DafnyRef#sec-synthesize-attr) for more detail.
".TrimStart());

    Add(ErrorId.c_abstract_type_cannot_be_compiled_extern,
    @"
The C++ compiler must be told how to translate an abstract type. Typically the value of the extern attribute is ""struct"".
Note that Dafny's C++ compiler is very preliminary, partial and experimental.
".TrimStart());

    Add(ErrorId.c_Go_unsupported_field,
    @"
_Documentation of the Go compiler errors is in progress._
".TrimStart());

    Add(ErrorId.c_Go_infeasible_conversion,
    @"
_Documentation of the Go compiler errors is in progress._
".TrimStart());
  }

  public static void RunStaticConstructor() {
  }
}
