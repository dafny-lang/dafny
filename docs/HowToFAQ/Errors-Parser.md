<!-- %check-resolve %default %useHeadings %check-ids -->

<!-- The file Errors-Parser.template is used along with Parser-Errors.cs to produce Errors-Parser.md.
     Errors-Parser.template holds the structure of the markdown file and the examples of each error message.
     Parser-Errors.cs holds the text of error explanations, so they are just in the source code rather than duplicated also in markdown.
     The content of Errors-Parser.template and Parser-Errors.cs are tied together by the errorids.
     Thus Errors-Parser.md is a generated file that should not be edited itself.
     The program make-error-catalog does the file generation.
-->

<!-- ./DafnyCore/Dafny.atg -->

## **Error: Duplicate declaration modifier: abstract** {#p_duplicate_modifier}

```dafny
abstract abstract module M {}
```

No Dafny modifier, such as [`abstract`, `static`, `ghost`](https://dafny.org/latest/DafnyRef/DafnyRef#sec-declaration-modifiers) may be repeated
Such repetition would be superfluous even if allowed.

## **Error: a _decl_ cannot be declared 'abstract'** {#p_abstract_not_allowed}
 
```dafny
abstract const c := 4
```

Only modules may be declared abstract.

## **Error: a function-by-method has a ghost function body and a non-ghost method body; a function-by-method declaration does not use the 'ghost' keyword.** {#p_no_ghost_for_by_method}

```dafny
ghost function f(): int
{
  42
} by method {
  return 42;
}
```

Functions with a [by method](https://dafny.org/latest/DafnyRef/DafnyRef#sec-function-declarations)
section to their body can be used both in ghost contexts and in non-ghost contexts; 
in ghost contexts the function body is used and in compiled contexts
the by-method body is used. The `ghost` keyword is not permitted on the
declaration.

## **Error: _decl_ cannot be declared 'ghost' (it is 'ghost' by default when using --function-syntax:3)** {#p_ghost_forbidden_default_3}

```dafny
module {:options "--function-syntax:3"} M {
  ghost function f(): int { 42 }
}
```

For versions prior to Dafny 4, the `function` keyword meant a ghost function
and `function method` meant a non-ghost function. 
From Dafny 4 on, `ghost function` means a ghost function and 
`function` means a non-ghost function. 
See the discussion [here](https://dafny.org/latest/DafnyRef/DafnyRef#sec-function-syntax) for
a discussion of options to control this feature.

## **Error: _decl_ cannot be declared 'ghost' (it is 'ghost' by default)** {#p_ghost_forbidden_default}

```dafny
module {:options "--function-syntax:4"} M {
  ghost least predicate p()
}
```

For versions prior to Dafny 4, the `function` keyword meant a ghost function
and `function method` meant a non-ghost function. 
From Dafny 4 on, `ghost function` means a ghost function and 
`function` means a non-ghost function. 
See the discussion [here](https://dafny.org/latest/DafnyRef/DafnyRef#sec-function-syntax) for
a discussion of options to control this feature.

## **Error: a _decl_ cannot be declared 'ghost'** {#p_ghost_forbidden}

```dafny
ghost module M {}
```

Only some kinds of declarations can be declared `ghost`, most often functions,
fields, and local declarations.

## **Error: a _decl_ cannot be declared 'static'** {#p_no_static}

```dafny
static module M {}
```

Only some kinds of declarations can be declared 'static', most often
fields, constants, methods, and functions, and only within classes.
Modules and the declarations within them are already always static.

## **Error: a _decl_ cannot be declared 'opaque'** {#p_no_opaque}

```dafny
opaque module M {}
```

Only some kinds of declarations can be declared 'opaque':
const fields and the various kinds of functions.

## **Warning: attribute _attribute_ is deprecated {#p_deprecated_attribute}

This attribute is obsolete and unmaintained. It will be removed from dafny in the future.

## **Error: argument to :options attribute must be a literal string** {#p_literal_string_required}

```dafny
module N { const opt := "--function-syntax:4" }
import opened N
module {:options opt} M{}
```

The value of an options attribute cannot be a computed expression. It must be a literal string.

## **Error: cannot declare identifier beginning with underscore** {#p_no_leading_underscore}

```dafny
function m(): (_: int) {0}
```

User-declared identifiers may not begin with an underscore;
such identifiers are reserved for internal use.
In match statements and expressions, an identifier
that is a single underscore is used as a wild-card match.

## **Error: sorry, bitvectors that wide (_number_) are not supported** {#p_bitvector_too_large}

```dafny
const b: bv2147483648
```

A bitvector type name is the characters 'bv' followed by a non-negative
integer literal. However, dafny only supports widths up to the largest
signed 32-bit integer (2147483647).

## **Error: sorry, arrays of that many dimensions (_number_) are not supported** {#p_array_dimension_too_large}

```dafny
const a: array2147483648<int>
```

A multi-dimensional array type name is the characters 'array' followed by
a positive integer literal. However, dafny only supports numbers of 
dimensions up to the largest signed 32-bit integer (2147483647).
In practice (as of v3.9.1) dimensions of more than a few can take 
overly long to resolve ([Issue #3180](https://github.com/dafny-lang/dafny/issues/3180)).

## **Error: There is no point to an export declaration at the top level** {#p_superfluous_export}

```dafny
export M
method M() {}
```

Although all top-level declarations are contained in an implicit top-level module, there is no syntax to import that module.
Such an import would likely cause a circular module dependency error.
If the implicit module cannot be imported, there is no point to any export declarations inside the implicit module.

## **Error: expected either a '{' or a 'refines' keyword here, found _token_** {#p_bad_module_decl}

<!-- %check-resolve %first -->
```dafny
module M {}
module N refine M {}
```

The [syntax for a module declaration](https://dafny.org/latest/DafnyRef/DafnyRef#sec-modules) is either `module M { ... }` or
`module M refines N { ... }` with optional attributes after the `module` keyword.
This error message often occurs if the `refines` keyword is misspelled.

## **Warning: the _name_ token is the identifier for the export set, not an adjective for an extreme predicate** {#p_misplaced_least_or_greatest}

<!-- %check-resolve-warn -->
```dafny
module M {
  export
  least predicate p()
}
```

A `least` or `greatest` token between `export` and `predicate` is a bit ambiguous:
it can be either the name of the export set or associated with the `predicate` declaration.
The parser associates it with the `export`. To avoid this warning, do not put the
`least` or `greatest` token on the same line as the `predicate` token.
If you intend for the `least` to go with the predicate, change the order of the declarations.

## **Error: no comma is allowed between provides and reveals and extends clauses in an export declaration** {#p_extraneous_comma_in_export}

```dafny
module M {
  export A reveals b, a, reveals b
  export B reveals b, a, provides b
  export C provides b, a, reveals b
  export D provides b, a, provides b
  const a: int
  const b: int
}
```

An export declaration consists of one or more `reveals`, `provides`, and extends clauses. Each clause contains
a comma-separated list of identifiers, but the clauses themselves are not separated by any delimiter.
So in the example above, the comma after `a` is wrong in each export declaration. 
This mistake is easy to make when the clauses are on the same line.

## **Error: fields are not allowed to be declared at the module level; instead, wrap the field in a 'class' declaration** {#p_top_level_field}

```dafny
module M {
  var c: int
}
```

`var` declarations are used to declare mutable fields of classes, local variables in method bodies, and identifiers in let-expressions.
But mutable field declarations are not permitted at the static module level, including in the (implicit) toplevel module.
Rather, you may want the declaration to be a `const` declaration or you may want the mutable field to be declared in the body of a class.

## **Warning: module-level functions are always non-instance, so the 'static' keyword is not allowed here** {#p_module_level_function_always_static}

<!-- %check-resolve-warn -->
```dafny
static predicate p() { true }
```

All names declared in a module (outside a class-like entity) are implicitly `static`.
Dafny does not allow them to be explictly, redundantly, declared `static`.

## **Warning: module-level methods are always non-instance, so the 'static' keyword is not allowed here** {#p_module_level_method_always_static}

<!-- %check-resolve-warn -->
```dafny
static method m() {}
```

All names declared in a module (outside a class-like entity) are implicitly `static`.
Dafny does not allow them to be explictly, redundantly, declared `static`.

## **Error: in refining a datatype, the '...' replaces the '=' token and everything up to a left brace starting the declaration of the body; only members of the body may be changed in a datatype refinement** {#p_bad_datatype_refinement}

```dafny
abstract module M { datatype D = A | B }
module N refines M { datatype D = ... Y | Z }
```

There are limitations on refining a datatype, namely that the set of constructors cannot be changed.
It is only allowed to add members to the body of the datatype.

## **Error: datatype extending traits is not yet enabled by default; use --general-traits=datatype to enable it** {#p_general_traits_datatype}

```dafny
trait Trait { }
datatype D extends Trait = A | B
```

A newtype extending a trait is not generally supported. The option --general-traits=full causes
Dafny to allow them in the input, but is not recommended.

## **Error: newtype extending traits is not fully supported (specifically, compilation of such types is not supported); to use them for verification only, use --general-traits=full** {#p_general_traits_full}

```dafny
trait Trait { }
newtype N extends Trait = int
```

Use of traits as non-reference types is supported, but is not yet the default. Until it becomes the
default, use --general--traits=datatype to enable it.

## **Warning: module-level const declarations are always non-instance, so the 'static' keyword is not allowed here {#p_module_level_const_always_static}

<!-- %check-resolve-warn -->
```dafny
static const i := 9
```

All names declared in a module (outside a class-like entity) are implicitly `static`.
Dafny does not allow them to be explictly, redundantly, declared `static`.

## **Error: expected an identifier after 'const' and any attributes** {#p_const_decl_missing_identifier}

```dafny
const c := 5
const
const d := 5
```

This error arises from a truncated declarations of a const field, namely just a const keyword.
To correct the error, add an identifier and either or both a type and initializing expression (or remove the const keyword).

## **Error: a const field should be initialized using ':=', not '='** {#p_bad_const_initialize_op}

```dafny
const c: int = 5
```

Dafny's syntax for initialization of const fields uses `:=`, not `=`.
In Dafny, `=` is used only in type definitions.

## **Error: a const declaration must have a type or a RHS value** {#p_const_is_missing_type_or_init}

```dafny
const i
```

A `const` declaration needs its type indicated by either an explicit type
or a right-hand-side expression, whose type is then the type of the 
declared identifier. 
So use syntax either like `const i: int` or `const i := 5` (or both together).

## **Error: in refining a newtype, the '...' replaces the '=' token and everything up to the left brace starting the declaration of the newtype body (if any); a newtype refinement may not change the base type of the newtype** {#p_misplaced_ellipsis_in_newtype}

```dafny
abstract module M { newtype T = int }
module N refines M { newtype T = ... int }
```

There are limitations on refining a newtype, namely that the base type cannot be changed. You can change an abstract type into a newtype, however.
When refining a newtype by adding a body, the ... stands in place of both the '=' and the base type.

## **Error: formal cannot be declared 'ghost' in this context** {#p_output_of_function_not_ghost}

```dafny
twostate function p(i: int): (ghost r: int) { true }
```

The output of a predicate or function cannot be ghost.
It is implicitly ghost if the function is ghost itself.

## **Error: formal cannot be declared 'new' in this context** {#p_no_new_on_output_formals}

```dafny
method m(i: int) returns (new r: int) { r := 0; }
```

The `new` modifier only applies to input parameters.

## **Error: formal cannot be declared 'nameonly' in this context** {#p_no_nameonly_on_output_formals}

```dafny
method m(i: int) returns (nameonly r: int) { r := 0; }
```

The `nameonly` modifier only applies to input parameters.

## **Error: formal cannot be declared 'older' in this context** {#p_no_older_on_output_formals}

```dafny
method m(i: int) returns (older r: int) { r := 0; }
```

The `older` modifier only applies to input parameters.

## **Error: a mutable field must be declared with a type** {#p_var_decl_must_have_type}

```dafny
class A {
  var f
  const g := 5
}
```

Because a mutable field does not have initializer, it must have a type (as in `var f: int`).
`const` declarations may have initializers; if they do they do not need an explicit type.

## **Error: a mutable field may not have an initializer** {#p_no_init_for_var_field}

```dafny
class A {
  var x: int := 6
  var y: int, x: int := 6, z: int
}
```

Dafny does not allow field declarations to have initializers. They are initialized in constructors.
Local variable declarations (which also begin with `var`) may have initializers.

## **Error: invalid formal-parameter name in datatype constructor** {#p_datatype_formal_is_not_id}

```dafny
datatype D = Nil | D(int: uint8) 
```

Datatype constructors can have formal parameters, declared with the usual syntax: 'name: type'.
In datatype constructors the 'name :' is optional; one can just state the type.
However, if there is a name, it may not be a typename.
The formal parameter name should be a simple identifier that is not a reserved word.

## **Error: use of the 'nameonly' modifier must be accompanied with a parameter name** {#p_nameonly_must_have_parameter_name}

```dafny
datatype D = D (i: int, nameonly int) {}
```

The parameters of a datatype constructor do not need to have names -- it is allowed to just give the type.
However, if `nameonly` is used, meaning the constructor can be called using named parameters,
then the name must be given, as in `datatype D = D (i: int, nameonly j: int) {}`

More detail is given [here](https://dafny.org/latest/DafnyRef/DafnyRef#sec-parameter-bindings).

## **Error: iterators don't have a 'returns' clause; did you mean 'yields'?** {#p_should_be_yields_instead_of_returns}

```dafny
iterator Count(n: nat) returns (x: nat) {
  var i := 0;
  while i < n {
    x := i;
    yield;
    i := i + 1;
  }
}
```

An [iterator](https://dafny.org/latest/DafnyRef/DafnyRef#sec-iterator-types) is like a co-routine: 
its control flow produces (yields) a value, but the execution continues from that point (a yield statement) to go on to produce the next value, rather than exiting the method. 
To accentuate this difference, a `yield` statement is used to say when the next value of the iterator is ready, rather than a `return` statement.
In addition, the declaration does not use `returns` to state the out-parameter, as a method would. Rather it has a `yields` clause.
The example above is a valid example if `returns` is replaced by `yields`.

## **Error: type-parameter variance is not allowed to be specified in this context** {#p_type_parameter_variance_forbidden}

```dafny
type List<T>
method m<+T>(i: int, list: List<T>) {}
method m<T,-U>(i: int, list: List<T>) {}
```

[Type-parameter variance](https://dafny.org/latest/DafnyRef/DafnyRef#sec-type-parameter-variance) is specified by a 
`+`, `-`, `*` or `!` before the type-parameter name.
Such designations are allowed in generic type declarations but not in generic method, function, or predicate declarations.

<!-- There are two instances of this error, one for the first item in a type parameter list, and one for subsequent items -->

## **Error: unexpected type characteristic: '000' should be one of == or 0 or 00 or !new** {#p_unexpected_type_characteristic}

```dafny
type T(000)
```

[Type characteristics](https://dafny.org/latest/DafnyRef/DafnyRef#sec-type-parameters), 
indicated in parentheses after the type name, state properties of the otherwise uninterpreted or abstract type.
The currently defined type characteristics are designated by `==` (equality-supporting), `0` (auto-initializable), `00` (non-empty), and `!new` (non-reference).

## **Error: extra comma or missing type characteristic: should be one of == or 0 or 00 or !new** {#p_missing_type_characteristic}

<!-- %no-check - TODO - fix to better error recovery after 4.0 -->
```dafny
type T(0,,0)
```

[Type characteristics](https://dafny.org/latest/DafnyRef/DafnyRef#sec-type-parameters), 
state properties of the otherwise uninterpreted or abstract type.
They are given in a parentheses-enclosed, comma-separated list after the type name.
The currently defined type characteristics are designated by `==` (equality - supporting),
`0` (auto - initializable), `00` (non - empty), and `!new` (non - reference).

## **Error: illegal type characteristic: '_token_' should be one of == or 0 or 00 or !new** {#p_illegal_type_characteristic}

```dafny
type T(X)
```

[Type characteristics](https://dafny.org/latest/DafnyRef/DafnyRef#sec-type-parameters),
indicated in parentheses after the type name, state properties of the otherwise uninterpreted or abstract type.
The currently defined type characteristics are designated by `==` (equality - supporting),
`0` (auto - initializable), `00` (non - empty), and `!new` (non - reference).
Type characteristics are given in a parentheses-enclosed, comma-separated list after the type name.

## **Warning: the old keyword 'colemma' has been renamed to the keyword phrase 'greatest lemma'** {#p_deprecated_colemma}

<!-- %check-resolve-warn -->
```dafny
colemma m() ensures true {}
```

The adjectives `least` and `greatest` for lemmas and functions are more consistent with the nomenclature for coinduction.

## **Warning: the old keyword phrase 'inductive lemma' has been renamed to 'least lemma'** {#p_deprecated_inductive_lemma}

<!-- %check-resolve-warn -->
```dafny
inductive lemma m() ensures true {}
```

The adjectives `least` and `greatest` for lemmas and functions are more consistent with the nomenclature for coinduction.

## **Error: constructors are allowed only in classes** {#p_constructor_not_in_class}

```dafny
module M {
  constructor M() {}
}
```

Constructors are methods that initialize class instances. That is, when a new instance of a class is being created, 
using the `new` object syntax, some constructor of the class is called, perhaps a default anonymous one.
So, constructor declarations only make sense within classes.

## **Error: a method must be given a name (expecting identifier)** {#p_method_missing_name}

```dafny
method {:extern "M"} (i: int) {}
```

A method declaration always requires an identifier between the `method` keyword and the `(` that starts the formal parameter list.
This is the case even when, as in the example above, a name is specified using `:extern`. The extern name is only used in the
compiled code; it is not the name used to refer to the method in Dafny code

## **Error: type of _k_ can only be specified for least and greatest lemmas** {#p_extraneous_k}

```dafny
lemma b[nat](i: int) { }
```

Least and greatest lemmas and predicates have a special parameter named `k`.
Its type is specified in square brackets between the lemma/predicate name and the rest of the signature.
The type may be either `nat` or `ORDINAL`.
But this type is specified only for `least` and `greatest` constructs.

## **Error: constructors cannot have out-parameters** {#p_constructors_have_no_out_parameters}

```dafny
class C {
  constructor (i: int) returns (j: int) {}
}
```

Constructors are used to initalize the state of an instance of a class.
Thus they typically set the values of the fields of the class instance.
Constructors are used in `new` object expressions, which return 
a reference to the newly constructed object (as in `new C(42)`).
There is no syntax to receive out-parameter values of a constructor
and they may not be declared. 
(This is similar to constructors in other programming languages, like Java.)

## **Error: A 'reads' clause that contains '*' is not allowed to contain any other expressions** {#p_reads_star_must_be_alone}

```dafny
const a: object
function f(): int
  reads a, *
{
  0
}
```

A reads clause lists the objects whose fields the function is allowed to read (or expressions 
containing such objects). `reads *` means the function may read anything.
So it does not make sense to list `*` along with something more specific.
If you mean that the function should be able to read anything, just list `*`.
Otherwise, omit the `*` and list expressions containing all the objects that are read.

## **Error: out-parameters cannot have default-value expressions** {#p_no_defaults_for_out_parameters}

```dafny
method m(i: int) returns (j: int := 0) { return 42; }
```

Out-parameters of a method are declared (inside the parentheses after the `returns` keyword)
with just an identifier and a type, separated by a colon. 
No initializing value may be given. If a default value is needed, assign the out-parameter
that value as a first statement in the body of the method.

## **Error: set type expects only one type argument** {#p_set_only_one_type_parameter}

```dafny
const c: set<int,bool>
```

A `set` type has one type parameter, namely the type of the elements of the set.
The error message states that the parser sees some number of type parameters different than one.
The type parameters are listed in a comma-separated list between `<` and `>`, after the type name.

## **Error: iset type expects only one type argument** {#p_iset_only_one_type_parameter}

```dafny
const c: iset<int,bool>
```

A `iset` type has one type parameter, namely the type of the elements of the set.
The error message states that the parser sees some number of type parameters different than one.
The type parameters are listed in a comma-separated list between `<` and `>`, after the type name.

## **Error: multiset type expects only one type argument** {#p_multiset_only_one_type_parameter}

```dafny
const c: multiset<int,bool>
```

A `multiset` type has one type parameter, namely the type of the elements of the multiset.
The error message states that the parser sees some number of type parameters different than one.
The type parameters are listed in a comma-separated list between `<` and `>`, after the type name.

## **Error: seq type expects only one type argument** {#p_seq_only_one_type_parameter}

```dafny
const c: seq<int,bool>
```

A `seq` type has one type parameter, namely the type of the elements of the sequence.
The error message states that the parser sees some number of type parameters different than one.
The type parameters are listed in a comma-separated list between `<` and `>`, after the type name.

## **Error: map type expects two type arguments** {#p_map_needs_two_type_parameters}

```dafny
const m: map<int,bool,string>
```

A `map` type has two type parameters: the type of the keys and the type of the values.
The error message states that the parser sees some number of type parameters different than two.

## **Error: imap type expects two type arguments** {#p_imap_needs_two_type_parameters}

```dafny
const m: imap<int,bool,string>
```

A `imap` type has two type parameters: the type of the keys and the type of the values.
The error message states that the parser sees some number of type parameters different than two.

## **Error: arrow-type arguments may not be declared as 'ghost'** {#p_no_ghost_arrow_type_arguments}

```dafny
const f: (ghost int, bool) -> int
```

[Arrow types](../DafnyRef/DafnyRef#sec-arrow-types) are the types of functions in Dafny.
They are designated with the arrow syntax, as shown in the example,
except that the types used cannot be declared as ghost.

## **Error: empty type parameter lists are not permitted** {#p_no_empty_type_parameter_list}

<!-- Not reachable -->

An instantiation of a generic type consists of the generic type name followed by a comma-separated
list of type arguments enclosed in angle brackets. If a type has no type arguments, then
there is no list and no angle brackets either.

However, this particular error message is not reachable in the current parser. 
If the message is seen, please report the code that caused it so that the bug or documentation can be corrected.

## **Error: a formal [ ] declaration is only allowed for least and greatest predicates** {#p_formal_ktype_only_in_least_and_greatest_predicates}

```dafny
predicate p[nat]() { true }
```

A declaration of an extreme predicate includes a special formal 
in addition to the regular parenthesis-enclosed list of formals.
The type of that special formal is given in square brackets between the 
predicate name and the opening parenthesis of the formals.
The type may be either `nat` or `ORDINAL`.
This special formal is not permitted in a regular (non-extreme) predicate.

## **Warning: the old keyword phrase 'inductive predicate' has been renamed to 'least predicate' {#p_deprecated_inductive_predicate}

<!-- %check-resolve-warn -->
```dafny
inductive predicate p()
```

The terms `least predicate` and `greatest predicate` are more descriptive of the relationship between them than was the old terminology.

## **Warning: the old keyword 'copredicate' has been renamed to the keyword phrase 'greatest predicate' {#p_deprecated_copredicate}

<!-- %check-resolve-warn -->
```dafny
copredicate p()
```

The terms `least predicate` and `greatest predicate` are more descriptive of the relationship between them than was the old terminology.

## **Error: a 'by method' implementation is not allowed on a twostate _what_** {#p_no_by_method_in_twostate}

```dafny
class Cell { var data: int  constructor(i: int) { data := i; } }
twostate predicate Increasing(c: Cell)
  reads c
{
  old(c.data) <= c.data
} by method {
  return old(c.data) <= c.data;
}
```

Two state functions and predicates are always ghost and do not have a compiled representation.
Such functions use values from two different program (heap) states, which is not 
something that can be implemented (at least with any degree of good performance) in conventional programming languages.

Because there is no feasible compiled verion of a two-state function, it cannot have a `by method` block (which is always compiled).

## **Error: a 'by method' implementation is not allowed on an extreme predicate** {#p_no_by_method_in_extreme_predicate}

```dafny
least predicate g() { 42 } by method { return 42; }
```

Least and greatest predicates are always ghost and do not have a compiled representation, 
so it makes no sense to have a `by method` alternative implementation.

## **Error: to use a 'by method' implementation with a _what_, declare _id_ using _what_, not '_what_ method'** {#p_no_by_method_for_ghost_function}

```dafny
function method m(): int {
  42
} by method {
  return 42;
}
```

`by method` constructs combine a ghost function (or predicate) with a non-ghost method.
The two parts compute the same result, and are verified to do so.
Uses of the function are verified using the function body, but the method body is used when the function is compiled.

Thus the function part is always implicitly `ghost` and may not be explicitly declared `ghost`.

## **Error: a _adjective_ _what_ is supported only as ghost, not as a compiled _what_** {#p_twostate_and_extreme_are_always_ghost}

```dafny
twostate function method m(): int {
  42
}
```

The `twostate`, `least`, and `greatest` functions and predicates are always ghost and cannot be compiled, so they cannot be
declared as a `function method` (v3 only).

## **Error: a _what_ is always ghost and is declared with '_what_'** {#p_old_ghost_syntax}

```dafny
module {:options "--function-syntax:experimentalPredicateAlwaysGhost"} M {
  predicate method p() { true }
}
```

This error only occurs when the `experimentalPredicateAlwaysGhost` option is chosen.
It indicates that `predicates` are always ghost and cannot be declared with the (Dafny 3) syntax `predicate method`.
- If you intend to predicate to be ghost, remove `method`.
- If you intend the predicate to be non-ghost, you either cannot use `experimentalPredicateAlwaysGhost` or you should use `function` with a `bool` return type instead of `predicate`

## **Error: the phrase '_what_ method' is not allowed when using --function-syntax:4; to declare a compiled predicate, use just 'predicate'** {#p_deprecating_predicate_method}

```dafny
module {:options "--function-syntax:4"} M {
  predicate method f() { true }
}
```

From Dafny 4 on, the phrases `function method` and `predicate method` are no
longer accepted. Use `function` for compiled, non-ghost functions and
`ghost function` for non-compiled, ghost functions, and similarly for predicates.
See [the documentation here](https://dafny.org/latest/DafnyRef/DafnyRef#sec-function-syntax).

## **Error: the phrase '_what_ method' is not allowed when using --function-syntax:4; to declare a compiled function, use just 'function'** {#p_deprecating_function_method}

```dafny
module {:options "--function-syntax:4"} M {
  function method f(): int { 42 }
}
```

From Dafny 4 on, the phrases `function method` and `predicate method` are no
longer accepted. Use `function` for compiled, non-ghost functions and
`ghost function` for non-compiled, ghost functions, and similarly for predicates.
See [the documentation here](https://dafny.org/latest/DafnyRef/DafnyRef#sec-function-syntax).

## **Error: there is no such thing as a 'ghost predicate method'** {#p_no_ghost_predicate_method}

```dafny
module {:options "--function-syntax:experimentalDefaultGhost"} M {
  ghost predicate method f() { true }
}
```

Pre-Dafny 4, a `function method` and a `predicate method` are explicitly
non-ghost, compiled functions, and therefore cannot be declared `ghost` as well.
If indeed the function or predicate is intended to be ghost, leave out `method`;
 if it is intended to be non-ghost, leave out `ghost`.

From Dafny 4 on, a ghost function is declared `ghost function` and a non-ghost function is declared `function` 
and there is no longer any declaration of the form `function method`, and similarly for predicates. 

See [the documentation here](../DafnyRef/DafnyRef#sec-function-syntax).

## **Error: there is no such thing as a 'ghost function method'** {#p_no_ghost_function_method}

```dafny
module {:options "--function-syntax:experimentalDefaultGhost"} M {
  ghost function method f(): int { 42 }
}
```

Pre-Dafny 4, a `function method` and a `predicate method` are explicitly
non-ghost, compiled functions, and therefore cannot be declared `ghost` as well.
If indeed the function or predicate is intended to be ghost, leave out `method`;
 if it is intended to be non-ghost, leave out `ghost`.

From Dafny 4 on, a ghost function is declared `ghost function` and a non-ghost function is declared `function` 
and there is no longer any declaration of the form `function method`, and similarly for predicates. 

See [the documentation here](../DafnyRef/DafnyRef#sec-function-syntax).

## **Error: a _what_ must be declared as either 'ghost _what_' or '_what_ method' when using --function-syntax:migration3to4** {#p_migration_syntax}

```dafny
module {:options "--function-syntax:migration3to4"} M {
  function f(): int { 42 }
}
```

This error occurs only when using `migration3to4`. With this option, ghost functions are declared using `ghost function` and compiled functions using `function method`.
Change `function` in the declaration to one of these.

## **Error: formal cannot be declared 'ghost' in this context** {#p_no_ghost_formal}

```dafny
ghost predicate p(ghost i: int) { true }
```

A ghost predicate or function effectively has all ghost formal parameters, so they cannot be declared ghost in addition.

## **Error: 'decreases' clauses are meaningless for least and greatest predicates, so they are not allowed** {#p_no_decreases_for_extreme_predicates}

```dafny
least predicate m(i: int)
  decreases i
{
  true
}
```

Least and greatest predicates are not checked for termination. In fact, unbounded recursion is part of being coinductive.
Hence `decreases` clauses are inappropriate and not allowed.

## **Error: _name_ return type should be bool, got _type_** {#p_predicate_return_type_must_be_bool}

```dafny
predicate b(): (r: boolean) { 4 }
```

A predicate is a function that returns `bool`. The return type here is something else.
If you mean to have a non-`bool` return type, use `function` instead of `predicate`.

## **Error: _name_s do not have an explicitly declared return type; it is always bool. Unless you want to name the result: ': (result: bool)'** {#p_no_return_type_for_predicate}

<!-- %no-check TODO - this example crashes -->
```dafny
predicate p(): bool { true } 
```

A `predicate` is simply a `function` that returns a `bool` value.
Accordingly, the type is (required to be) omitted, unless the result is being named.
So `predicate p(): (res: bool) { true }` is permitted.

## **Error: A '*' expression is not allowed here** {#p_no_wild_expression}

```dafny
function m(i: int): int
  decreases *
{
  42
}
```

A method or loop with a `decreases *` clause is not checked for termination.
This is only permitted for non-ghost methods and loops.
Insert an actual decreases expression.

## **Error: A '*' frame expression is not permitted here** {#p_no_wild_frame_expression}

```dafny
iterator Gen(start: int) yields (x: int)
  reads *
{
  var i := 0;
  while i < 10 invariant |xs| == i {
    x := start + i;
    yield;
    i := i + 1;
  }
}
```

A `reads *` clause means the reads clause allows the functions it specifies to read anything.
Such a clause is not allowed in an iterator specification.
Insert a specific reads expression.

## **Warning: _kind_ refinement is deprecated** {#p_deprecated_statement_refinement}

<!-- TODO -->

Statement refinement has been deprecated. Refinement is restricted to changing declarations, not bodies of methods or functions.

## **Error: invalid statement beginning here (is a 'label' keyword missing? or a 'const' or 'var' keyword?)** {#p_invalid_colon}

```dafny
method m(n: nat) {
  x: while (0 < n) { break x; }
}
```

In this situation the parser sees the identifier (x) and the following colon.
This is not a legal start to a statement. Most commonly either
* a `var` or `const` keyword is missing, and the `x:` is the beginning of a declaration, or
* a `label` keyword is missing and the identifier is the label for the statement that follows.
(The second error is somewhat common because in C/C++ and Java, there is no keyword introducing a label, just the identifier and the colon.)

## **Error: An initializing element display is allowed only for 1-dimensional arrays** {#p_initializing_display_only_for_1D_arrays}

```dafny
method m() {
  var a := new int[2,2] [1,2,3,4];
}
```

One-dimensional arrays can be initialized like `var s := new int[][1,2,3,4];`,
but multi-dimensional arrays cannot. The alternatives are to initialize the array
in a loop after it is allocated, or to initialize with a function, as in
`var a:= new int[2,2]((i: int, j: int)=>i+j)`.

## **Error: a local variable should be initialized using ':=', ':-', or ':|', not '='** {#p_no_equal_for_initializing}

```dafny
method m() {
  var x = 5;
}
```

Local variables are initialized with `:=` (and sometimes with `:-` or `:|`), but not with `=`.
In Dafny `=` is used only in type definitions.

## **Error: LHS of assign-such-that expression must be variables, not general patterns** {#p_no_patterns_and_such_that}

```dafny
datatype D = D(x: int, y: int)
method m() {
  var D(x,y) :| x + y == 5;
}
```

The `:|` syntax is called _assign-such-that_: the variables on the left-hand-side are initialized or assigned
some non-deterministic values that satisfy the predicate on the right-hand-side.

However, Dafny only allows a list of simple variables on the left, not datatype deconstructor patterns, as seen here.

## **Error: 'modifies' clauses are not allowed on refining loops** {#p_no_modifies_on_refining_loops}

<!-- TODO _ example -->

_Refining statements, including loops, are deprecated._

## **Error: Expected 'to' or 'downto'** {#p_to_or_downto}

```dafny
method m(n: nat) {
  for i := n DownTo 0 {}
}
```

A for loop can express a computation to be performed for each value of a _loop index_.
In Dafny, the loop index is an int-based variable that is either 
- incremented up from a starting value to just before an ending value: `3 to 7` means 3, 4, 5, and 6
- or decremented from just below a starting value down to an ending value: `7 downto 3` means 6, 5, 4, and 3.

The contextual keywords `to` and `downto` indicate incrementing and decrementing, respectively.
No other words are allowed here, including writing them with different case.

These two words have special meaning only in this part of a for-loop; they are not reserved words elsewhere.
That is, the code
<!-- %check-resolve %exit 0 %nomsg -->
```dafny
method m() {
  var to: int := 6;
  var downto: int := 8;
  for to := to to downto {}
}
```
is legal, but not at all recommended.

## **Error: A 'decreases' clause that contains '*' is not allowed to contain any other expressions** {#p_no_decreases_expressions_with_star}

```dafny
method f(n: int) returns (r: int)
  decreases *, n
{
  r := if n == 0 then n else -1-f(n-1);
}
```

A `decreases` clause provides a metric that must decrease from one call to the next, 
in order to assure termination of a sequence of recursive calls. 
In loops it assures termination of the loop iteration.

`decreases *` means to skip the termination check.
So it does not make sense to both list a metric and to list '*'.
Use one or the other.

## **Error: expected either 'by' or a semicolon following the assert expression** {#p_assert_needs_by_or_semicolon}

```dafny
method m() {
  assert true
}
```

Assert statements, like all statements, end in either a semicolon or a block. Most assert statements end in semicolons,
but an assert-by statement has the form `assert expr by { ... }` where the by-block contains statements such as lemma calls
that assist in proving the validity of the asserted expression.

## **Warning: a forall statement with no bound variables is deprecated; use an 'assert by' statement instead** {#p_deprecated_forall_with_no_bound_variables}

<!-- TODO -->

## **Warning: the modify statement with a block statement is deprecated** {#p_deprecated_modify_statement_with_block}

<!-- TODO-->

## **Error: the main operator of a calculation must be transitive** {#p_calc_operator_must_be_transitive}

```dafny
lemma abs(a: int, b: int, c: int)
  ensures a + b + c == c + b + a
{
  calc != {
    a + b + c;
    a + c + b;
    c + a + b;
  }
}
```

A [calc statement](../DafnyRef/DafnyRef#sec-calc-statement)
contains a sequence of expressions interleaved by operators.
Such a sequence aids the verifier in establishing a desired conclusion.
But the sequence of operators must obey certain patterns similar to chaining expressions.
In this case a default operator is stated (the `!=` between `calc` and `{`).
This default operator is the implicit operator between each consecutive pair of expressions
in the body of the calc statement.

But the operator has to be transitive: `!=` is not allowed; `==`, `<`, `<=`, '>' and '>=' are allowed.

## **Error: this operator cannot continue this calculation** {#p_invalid_calc_op_combination}

```dafny
lemma abs(a: int, b: int, c: int)
  ensures a + b + c == c + b + a
{
  calc {
    a + b + c;
    !=
    a + c + b;
    !=
    c + a + b;
  }
}
```

A [calc statement](../DafnyRef/DafnyRef#sec-calc-statement)
contains a sequence of expressions interleaved by operators.
Such a sequence aids the verifier in establishing a desired conclusion.
But the sequence of operators must obey certain patterns similar to chaining expressions.

In particular, this error message is complaining that it sees an unacceptable operator.
In this case, the reason is that the sequence may contain only one `!=` operator;
another reason causing this message would be a combination of `<` and `>` operators.

## **Error: a calculation cannot end with an operator** {#p_calc_dangling_operator}

```dafny
lemma abs(a: int, b: int, c: int)
  ensures a + b + c == c + b + a
{
  calc {
    a + b + c;
    ==
  }
}
```

A [calc statement](../DafnyRef/DafnyRef#sec-calc-statement)
contains a sequence of expressions interleaved by operators.
Such a sequence aids the verifier in establishing a desired conclusion.
But the sequence must begin and end with (semicolon-terminated) expressions.

This error message is complaining that it sees an operator ending the sequence.
This may be because there is no following expression or that the parser 
does not recognize the material after the last operator as a legal ending expression.

## **Error: Calls with side-effects such as constructors are not allowed in expressions.** {#p_no_side_effects_in_expressions}

```dafny
class A { function f(): int { 0 } }
const c := (new A).f()
```

Dafny expressions may not have side-effects. This prohibits both assignments to local variables and any
changes to the heap. Thus method and constructor calls may not occur in expressions.
This check is syntactic, so even methods that do not modify anything are not permitted in expressions.

## **Error: Ambiguous use of ==> and <==. Use parentheses to disambiguate.** {#p_ambiguous_implies}

```dafny
const b := true <== false ==> true
```

The `==>` and `<==` operators have the same precedence but do not associate with each other.
You must use parentheses to show how they are grouped. Write `p ==> q <== r` as either
`(p ==> q) <== r` or `p ==> (q <== r)`.

In contrast, `p ==> q ==> r` is `p ==> (q ==> r)` and
`p <== q <== r` is `(p <== q) <== r`.

See [this section](../DafnyRef/DafnyRef#sec-implication-and-reverse-implication) for more information.

## **Error: Ambiguous use of ==> and <==. Use parentheses to disambiguate.** {#p_ambiguous_implies_2}

```dafny
const b := true ==> false <== true
```

The `==>` and `<==` operators have the same precedence but do not associate with each other.
You must use parentheses to show how they are grouped. Write `p ==> q <== r` as either
`(p ==> q) <== r` or `p ==> (q <== r)`.

In contrast, `p ==> q ==> r` is `p ==> (q ==> r)` and
`p <== q <== r` is `(p <== q) <== r`.

See [this section](../DafnyRef/DafnyRef#sec-implication-and-reverse-implication) for more information.

<!-- There are two instances of this error, one in which the first operator is ==> and one in which it is <== -->

## **Error: Ambiguous use of && and ||. Use parentheses to disambiguate.** {#p_ambiguous_and_or}

```dafny
const b := true && false || true
```

The `&&` and `||` operators have the same precedence but do not associate with each other.
You must use parentheses to show how they are grouped. Write `p && q || r` as either
`(p && q) || r` or `p && (q || r)`.

## **Error: chaining not allowed from the previous operator** {#p_invalid_equal_chaining}

```dafny
const c := 1 in {1} == true
```

[Chained operations](../DafnyRef/DafnyRef#sec-basic-types)
are a sequence of binary operations without parentheses: _a op b op c op d op e_.
But there are limitations on which operators can be in one chain together.

In particular, the relational operators `in` and `!in` may not be part of a chain.
Use parentheses as necessary to group the operations.

## **Error: a chain cannot have more than one != operator** {#p_invalid_notequal_chaining}

```dafny
const c := 1 != 2 != 3
```

[Chained operations](../DafnyRef/DafnyRef#sec-basic-types)
are a sequence of binary operations without parentheses: _a op b op c op d op e_.
But there are limitations on which operators can be in one chain together.

In particular for this error message, one cannot have chains that include more than one `!=` operator.

## **Error: this operator cannot continue this chain** {#p_invalid_operator_in_chain}

```dafny
const c := {} !! {} != {}
```

[Chained operations](../DafnyRef/DafnyRef#sec-basic-types)
are a sequence of binary operations without parentheses: _a op b op c op d op e_.
But there are limitations on which operators can be in one chain together.

In particular for this error message, the designated operator is not permitted to extend the existing chain.

## **Error: this operator chain cannot continue with an ascending operator** {#p_invalid_descending_chaining}

```dafny
const c := 2 > 3 < 4
```

[Chained operations](../DafnyRef/DafnyRef#sec-basic-types)
are a sequence of binary operations without parentheses: _a op b op c op d op e_.
But there are limitations on which operators can be in one chain together.

In particular for this error message, one cannot have chains that include both
less-than operations (either `<` or `<=`) and greater-than operations (either `>` or `>=`).

## **Error: this operator chain cannot continue with a descending operator** {#p_invalid_ascending_chaining}

```dafny
const c := 2 < 3 > 4
```

[Chained operations](../DafnyRef/DafnyRef#sec-basic-types)
are a sequence of binary operations without parentheses: _a op b op c op d op e_.
But there are limitations on which operators can be in one chain together.

In particular for this error message, one cannot have chains that include both
less-than operations (either `<` or `<=`) and greater-than operations (either `>` or `>=`).

## **Error: can only chain disjoint (!!) with itself** {#p_invalid_disjoint_chaining}

```dafny
const c := 2 < 3 !! 4
```

[Chained operations](../DafnyRef/DafnyRef#sec-basic-types)
are a sequence of binary operations without parentheses: _a op b op c op d op e_.
But there are limitations on which operators can be in one chain together.

In particular for this error message, a disjoint operator (`!!`) can appear in a chain
only if all the operators in the chain are disjoint operators.

As described [here](../DafnyRef/DafnyRef#sec-collection-types),
`a !! b !! c !! d` means that `a`, `b`, `c`, and `d` are all mutually disjoint
(which is a different rewriting of the chain than for other operations).

## **Error: this operator cannot be part of a chain** {#p_operator_does_not_chain}

```dafny
const c := 2 < 3 in 4
```

The operators `in` and `!in` are relational operators, but they may not occur in a chain.
Use parentheses if necessary. Such expressions are usually not type-correct in any case.

## **Error: invalid relational operator** {#p_bang_not_a_relational_op}

```dafny
const s : set<int>
const r := s ! s
```

The parser is expecting a relational expression, that is, two expressions separated by a relational operator
(one of `==`, `!=`, `>`, `>=`, `<`, `<=`, `!!`, `in`, `!in`). But the parser saw just a `!` ,
which could be the beginning of `!=`, `!!`, or `!in`, but is not continued as such.
So perhaps there is extraneous white space or something else entirely is intended.

## **Error: invalid relational operator (perhaps you intended \"!!\" with no intervening whitespace?)** {#p_invalid_relational_op}

```dafny
const s : set<int>
const r := s ! ! s
```

The parser is expecting a relational expression, that is, two expressions separated by a relational operator
(one of `==`, `!=`, `>`, `>=`, `<`, `<=`, `!!`, `in`, `!in`). But the parser saw two `!` separated by
white space. This is possibly meant to be a `!!` operator, but it could also just be an illegal expression.

## **Error: Ambiguous use of &, |, ^. Use parentheses to disambiguate.** {#p_ambiguous_bitop}

```dafny
const i: int := 5 | 6 & 7
```

The bit-operators `&`, `|`, and `^` have the same precedence but do not associate with each other.
So if they are used within the same expression, parentheses have to be used to show how they
are grouped. The example `5 | 6 & 7` should be written as either `(5 | 6) & 7` or `5 | (6 & 7)`.

## **Error: too many characters in character literal** {#p_invalid_char_literal}

<!-- %check-resolve %options --allow-deprecation --unicode-char:false -->
```dafny
const c := '🚀'
```

A character literal can only contain a single value of the built-in char type.
When --unicode-char is disabled, the char type represents UTF-16 code units, 
so this means a character literal can only contain a character that can be represented
with a single such unit, i.e. characters in the Basic Multilingual Plane. 
The rocket ship emoji ('🚀'), for example, is encoded with two surrogate code points.

This can be fixed by enabling the --unicode-char mode, as that defines char as any
Unicode scalar value, but be aware that it may change the meaning of your program.

More detail is given [here](../DafnyRef/DafnyRef#sec-character-constant-token) and [here](../DafnyRef/DafnyRef#sec-escaped-characters).;

## **Error: binding not allowed in parenthesized expression** {#p_no_parenthesized_binding}

```dafny
method m() {
  var c := ( 4 := 5 );
}
```

Bindings of the form `x := y` are used in map-display expressions, in which case they are enclosed in square brackets,
not parentheses. `var c := ( 4 := 5 )` should be `var c := map[ 4 := 5 ]`.

## **Error: A forming expression must be a multiset** {#p_must_be_multiset}

A set/iset/multiset display expression can have two forms. 
One form is a list of values enclosed by curly braces: `var c := multiset{1,2,2,3}`.
The other appears as a conversion operation: `var c := multiset(s)`.
However, this second form can only be used to convert a set to a multiset.

In the current parser, however, this error message is unreachable,
so if it appears please report the error.
The tests that check for this error case are already known to be false by previous testing.

## **Error: seq type expects only one type argument** {#p_seq_display_has_one_type_argument}

```dafny
const c := seq<int,int>(5, i=>i)
```

The built-in `seq` (sequence) type takes one type parameter, which in some situations is inferred.
That type parameter is the type of the sequence elements.

## **Error: a map comprehension with more than one bound variable must have a term expression of the form 'Expr := Expr'** {#p_map_comprehension_must_have_term_expression}

```dafny
const s := map x, y  | 0 <= x < y < 10 :: x*y
```

A map comprehension defines a map, which associates a value with each member of a set of keys.
The full syntax for a map comprehension looks like `map x | 0 <= x < 5 :: x*2 := x*3`
which maps the keys `0, 2, 4, 6, 8` to the values `0, 3, 6, 9, 12` respectively.

One can abbreviate the above syntax to expressions like `map x | 0 <= x < 5 :: x*3`,
which is equivalent to `map x | 0 <= x < 5 :: x := x*3`. The missing expression before
the `:=` is just the declared identifier.

One can also have multiple variables involved as in `map x, y | 0 < x < y < 5 :: 10*x+y := 10*y+x`,
which defines the mappings `(12=>21, 13=>31, 14=>41, 23=>32, 24=>42, 34=>43)`.

But when there are multiple variables, one cannot abbreviate the `:=` syntax with just its right-hand expression,
because it is not clear what the left-hand expression should be. 

Incorrect text like `const s := map x, y | 0 <= x < y < 10 :: x*y` should be written
as `const s := map x, y | 0 <= x < y < 10 :: f(x,y) := x*y` for some `f(x,y)` that gives
a unique value for each pair of `x,y` permitted by the range expression (here `0 <= x < y < 10`).

## **Error: LHS of let-such-that expression must be variables, not general patterns** {#p_no_patterns_in_let_such_that}

```dafny
datatype Data = D(i: int, j: int)
const c: int := var Data(d,dd) :| d == 10 && dd == 11; d
```

The let-such-that expression initializes a variable to some value satisfying a given condition.
For example, one might write `const cc := var x: int :| x <= 10; x`,
where `cc` would get some value `x` satisfying `x < 10`.

For simplicity, however, Dafny requires the variables being initialized to be simple names, not patterns.

## **Error: a variable in a let expression should be initialized using ':=', ':-', or ':|', not '='** {#p_no_equal_in_let_initialization}

```dafny
method m() {
  var x := var y = 5; y*y;
}
```

Like local variables, let variables are initialized with `:=` (and sometimes with `:-` or `:|`), but not with `=`.
In Dafny `=` is used only in type definitions.

## **Error: ':-' can have at most one left-hand side** {#p_elephant_has_one_lhs}

```dafny
datatype Outcome<T> = 
  | Success(value: T) 
  | Failure(error: string) 
{ predicate IsFailure() { this.Failure? } 
  function PropagateFailure<U>(): Outcome<U> 
    requires IsFailure() 
  { Outcome<U>.Failure(this.error) // this is Outcome<U>.Failure(...) 
  }
 
  function Extract(): T requires !IsFailure() { this.value } 
}

function m(): Outcome<int> { Outcome<int>.Success(0) }
function test(): Outcome<int> {
  var rr, rrr :- m(); Outcome.Success(1) 
}
```

Within a function, the `:-` operator is limited to a most one left-hand-side and exactly one-right-hand-side.

## **Error: ':-' must have exactly one right-hand side** {#p_elephant_has_one_rhs}

```dafny
datatype Outcome<T> = 
  | Success(value: T) 
  | Failure(error: string) 
{ predicate IsFailure() { this.Failure? } 
  function PropagateFailure<U>(): Outcome<U> 
    requires IsFailure() 
  { Outcome<U>.Failure(this.error) // this is Outcome<U>.Failure(...) 
  }
 
  function Extract(): T requires !IsFailure() { this.value } 
}

function m(): Outcome<int> { Outcome<int>.Success(0) }
function test(): Outcome<int> {
  var rr :- m(), 44; Outcome.Success(1) 
}
```

This error only occurs when using the elephant operator `:-` in conjunction with
[failure-compatible types](../DafnyRef/DafnyRef#sec-failure-compatible-types)
and in the context of a let-or-fail expression.

In contrast to the let expression (`:=`), which allows multiple parallel initializations, 
the let-or-fail expression (`:-`) is implemented to
only allow at most a single left-hand-side and exactly one right-hand-side.

## **Error: a set comprehension with more than one bound variable must have a term expression** {#p_set_comprehension_needs_term_expression}

```dafny
const s := set x, y | 0 <= x < y < 10 
```

A set comprehension (1) declares one or more variables, (2) possibly states some limits on those variables, 
and (3) states an expression over those variables that are the values in the set.

If there is no expression, then the expression is taken to be just the _one_ declared variable.
For instance one could write `set b: bool`, which is equivalent to `set b: bool :: b` and would be the set of all `bool` values.
Another example is `set x: nat | x < 5, which is equivalent to `set x: nat | x < 5:: x` and would be the set `{0, 1, 2, 3, 4}`.

But if more than one variable is declared, then there is no natural implicit expression to fill in after the `::` if it is omitted, 
so some expression is required. The failing example above, for example, might use the expression `x * y`, as in 
`set x, y  | 0 <= x < y < 10 :: x * y`, or any other expression over `x` and `y`.

## **Warning: opaque is deprecated as an identifier. It will soon become a reserved word. Use a different name.** {#p_deprecated_opaque_as_identifier}

<!-- %check-resolve-warn -->
```dafny
const opaque: int
```

Because of the value to proof success of using `opaque` declarations and `reveal`ing them in appropriate contexts,
the word `opaque` is being converted to a reserved keyword, whereas it used to be a normal identifier.
Please rename your use of opaque as an identifier to some other name.

## **Error: invalid name after a '.'** {#p_invalid_name_after_dot}

This error message is not reachable in current Dafny.
If it occurs, please report an internal bug (or obsolete documentation).

## **Error: cannot declare identifier beginning with underscore** {#p_no_leading_underscore_2}

```dafny
const _myconst := 5
```

User-declared identifiers may not begin with an underscore;
such identifiers are reserved for internal use.
In match statements and expressions, an identifier
that is a single underscore is used as a wild-card match.

## **Warning: deprecated style: a semi-colon is not needed here {#p_deprecated_semicolon}

<!-- %check-resolve %options -->
```dafny
const c := 5;
```

Semicolons are required after statements and declarations in method bodies,  
but are deprecated after declarations within modules and types.

## **Error: incorrectly formatted number** {#p_bad_number_format}

<!-- not reachable -->

This error can only result from an internal bug in the Dafny parser.
The parser recognizes a legitimate sequence of digits (as an integer literal
and then passes that string to a library routine to create a BigInteger
or BigDecimal. Given the parser logic, that parsing should never fail.

## **Error: incorrectly formatted number** {#p_bad_hex_number_format}

<!-- not reachable -->

This error can only result from an internal bug in the Dafny parser.
The parser recognizes a legitimate sequence of hexdigits
and then passes that string to a library routine to create a BigInteger. 
Given the parser logic, that parsing should never fail.

## **Error: incorrectly formatted number** {#p_bad_decimal_number_format}

<!-- not reachable -->

This error can only result from an internal bug in the Dafny parser.
The parser recognizes a legitimate Dafny decimal number 
and then passes that string to a library routine to create a BigDecimal. 
Given the parser logic, that parsing should never fail.

<!-- FILE ./DafnyCore/CoCo/Parser.frame -->

## **Error: invalid _entity_** {#p_generic_syntax_error}

<!-- TODO -->

This "invalid something" message where the something is typically
the name of an internal parser non-terminal means that the text being parsed
is a badly malformed instance of whatever parser entity was being parsed.
This is an automatically generated message by the CoCo parser generator
for a situation in which no specific recovery or a
more informative error message has been implemented.

The only advice we can give is to carefully scrutinize the location of the
error to see what might be wrong with the text. If you think this is a
common or confusing enough occurrence to warrant special error handling,
please suggest the improvement, with this sample code, to the Dafny team.

<!-- FILE ./DafnyCore/CoCo/Scanner.frame -->

## **Error: Malformed _template_ pragma: #_source_** {#sc_malformed_pragma}

<!-- %no-check -->
```dafny
const s := @"
#line S
"
```

This pragma syntax is no longer supported. If this message is seen, please report it to the Dafny development team.
The Dafny scanner once supported pragmas of the form `#line <lineno> <filename>`, with the filename optional.
This message indicates that the pragma was not readable, most likely because the line number was not a
parsable numeral.

## **Error: Unrecognized pragma: #_source_** {#sc_unknown_pragma}

<!-- %no-check -->
```dafny
const s := @"
# I love hashes
"
```

This pragma syntax is no longer supported. If this message is seen, please report it to the Dafny development team.
The Dafny scanner saw a pragma -- the first character of the line is a # character. But it is not one that the
scanner recognizes. The only pragma ever recognized was `#line`.

<!-- ./DafnyCore/AST/Grammar/ProgramParser.cs -->

## **Error: [internal error] Parser exception: _message_** {#p_internal_exception}

This error indicates an internal crashing bug in Dafny. Please report it with as much of 
the source code that causes the problem as possible.
