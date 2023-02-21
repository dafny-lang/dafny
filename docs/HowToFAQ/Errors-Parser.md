<!-- %check-resolve %default %useHeadings -->

<!-- Parser.cs, but not Deprecated warnings or syntactic errors -->

## **Error: Duplicate declaration modifier: abstract** {#p_duplicate_modifier}

```dafny
abstract abstract module M {}
```

No Dafny modifier, such as [`abstract`, `static`, `ghost`](../DafnyRef/DafnyRef#sec-declaration-modifiers) may be repeated
Such repetition would be superfluous even if allowed.

## **Error: a _decl_ cannot be declared 'abstract'** {#p_abstract_not_allowed}
 
```dafny
module M {
  abstract const c := 4
}
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

## **Error: _decl_ cannot be declared 'ghost' (it is 'ghost' by default when using --function-syntax:3)** {#p_ghost_forbidden_default}

```dafny
module {:options "--function-syntax:3"} M {
  ghost function f(): int { 42 }
}
```

For versions prior to Dafny 4, the `function` keyword meant a ghost function
and `function method` meant a non-ghost function. 
From Dafny 4 on, `ghost function` means a ghost function and 
`function` means a non-ghost function. 
See the discussion [here](../DafnyRef/DafnyRef#sec-function-syntax) for
a discussion of options to control this feature.

## **Error: a _decl_ cannot be declared 'ghost'** {#p_ghost_forbidden}

```dafny
ghost module M {}
```

Only some kinds of declarations can be declared `ghost`, most often functions,
fields, and local declarations. In the example, a `module` may not be `ghost`.

## **Error: a _decl_ cannot be declared 'static'** {#p_no_static}

```dafny
static module M {}
```

Only some kinds of declarations can be declared 'static', most often 
fields, constants, methods, and functions, and only within classes.
Modules and the declarations within them are already always static.

## **Warning: Attribute _attribute_ is deprecated and will be removed in Dafny 4.0 {#p_deprecated_attribute}

<!-- %check-resolve-warn -->
```dafny
method {:handle} m() {}
```

The `{:handle}` and `{:dllimport}` attributes are obsolete and unmaintained. They will be removed.

## **Error: argument to :options attribute must be a literal string** {#p_literal_string_required}

```dafny
module N { const opt := "--function-syntax:4" }
import opened N
module {:options opt} M{}
```

The value of an options attribute cannot be a computed expression. It must be a literal string.

## **Error: cannot declare identifier beginning with underscore** {#p_no_leading_underscore}

```dafny
const _myconst := 5
function m(): (_: int) {0}
```

User-declared identifiers may not begin with an underscore; 
such identifiers are reserved for internal use. 
In match statements and expressions, an identifier
that is a single underscore is used as a wild-card match.

<!-- There are two instances of this message. An example of the other message is
     function m(): (_: int) {0}
-->

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

```dafny
module M {}
module N refine M {}
```

The [syntax for a module declaration](../DafnyRef/DafnyRef#sec-modules) is either `module M { ... }` or
`module M refines N { ... }` with optional attributes after the `module` keyword.
This error message often occurs if the `refines` keyword is misspelled.

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

## **Error: in refining a datatype, the '...' replaces the '=' token and everything up to a left brace starting the declaration of the body; only members of the body may be changed in a datatype refinement** {#p_bad_datatype_refinement}

```dafny
abstract module M { datatype D = A | B }
module N refines M { datatype D = ... Y | Z }
```

There are limitations on refining a datatype, namely that the set of constructors cannot be changed.
It is only allowed to add members to the body of the datatype.

## **Error: mutable fields are not allowed in value types** {#p_no_mutable_fields_in_value_types}

```dafny
datatype D = A | B  { var c: D }
```

The `var` declaration declares a mutable field, which is only permitted within
classes, traits and iterators. 
`const` declarations can be members of value-types, such as datatypes.

## **Error: a const field should be initialized using ':=', not '='** {#p_bad_const_initialize_op}

```dafny
const c: int = 5
```

Dafny's syntax for initialization and assignment uses `:=`, not `=`.
In Dafny `=` is used only in type definitions.

## **Error: a const declaration must have a type or a RHS value** {#p_const_is_missing_type_or_init}

```dafny
const i
```

A `const` declaration needs its type indicated by either an explicit type
or a right-hand-side expression, whose type is then the type of the 
declared identifier. 
So use syntax either like `const i: int` or `const i:= 5` (or both together).

## **Error: in refining a newtype, the '...' replaces the '=' token and everything up to the left brace starting the declaration of the newtype body (if any); a newtype refinement may not change the base type of the newtype** {#p_misplaced_ellipsis_in_newtype}

```dafny
abstract module M { newtype T = int }
module N refines M { newtype T = ... int }
```

There are limitations on refining a newtype, namely that the base type cannot be changed. You can change an opaque type into a newtype, however.

## **Error: formal cannot be declared 'ghost' in this context** {#p_output_of_function_not_ghost}

```dafny
predicate m(i: int): (ghost r: bool) { 0 }
```

The output of a predicate or function cannot be ghost.
It is implicitly ghost if the function is ghost itself.

<!-- MISPLACED TODO -->
## **Error: formal cannot be declared 'ghost' in this context** {#p_ghost_function_output_not_ghost}

```dafny
ghost function m(ghost i: int): int {
  42
}
```

If a method, function, or predicate is declared as ghost, then its formal parameters may not also be declared ghost.
Any use of this construct will always be in ghost contexts.

## **Error: formal cannot be declared 'new' in this context** {#p_no_new_on_output_formals}

```dafny
method m(i: int) returns (new r: int) {}
```

The `new` modifier only applies to input parameters.

## **Error: formal cannot be declared 'nameonly' in this context** {#p_no_nameonly_on_output_formals}

```dafny
method m(i: int) returns (nameonly r: int) {}
```

The `nameonly` modifier only applies to input parameters.

## **Error: formal cannot be declared 'older' in this context** {#p_no_older_on_output_formals}

```dafny
method m(i: int) returns (older r: int) {}
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
However, if there is a name, it may not be a typename, as in the failing example above.
The formal parameter name should be a simple identifier that is not a reserved word.


## **Error: use of the 'nameonly' modifier must be accompanied with a parameter name** {#p_nameonly_must_have_parameter_name}

```dafny
datatype D = D (i: int, nameonly int) {}
```

The parameters of a datatype constructor do not need to have names -- it is allowed to just give the type.
However, if `nameonly` is used, meaning the constructor can be called using named parameters,
then the name must be given, as in `datatype D = D (i: int, nameonly j: int) {}`

More detail is given [here](../DafnyRef/DafnyRef#sec-parameter-bindings).

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

An [iterator](../DafnyRef/DafnyRef#sec-iterator-types) is like a co-routine: 
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

[Type-parameter variance](../DafnyRef/DafnyRef#sec-type-parameter-variance) is specified by a 
`+`, `-`, `*` or `!` before the type-parameter name.
Such designations are allowed in generic type declarations but not in generic method, function, or predicate declarations.

<!-- There are two instances of this error, one for the first item in a type parameter list, and one for subsequent items -->

## **Error: unexpected type characteristic: '000' should be one of == or 0 or 00 or !new** {#p_unexpected_type_characteristic}

```dafny
type T(000)
```

[Type parameters](../DafnyRef/DafnyRef#sec-type-parameters), 
indicated in parentheses after the type name, state properties of the otherwise uninterpreted or opaque type.
The currently defined type parameters are designated by `==` (equality-supporting), `0` (auto-initializable), `00` (non-empty), and `!new` (non-reference).

## **Error: extra comma or missing type characteristic: should be one of == or 0 or 00 or !new** {#p_missing_type_characteristic}

<!-- %no-check - TODO - fix to better error recovery after 4.0 -->
```dafny
type T(0,,0)
```

[Type parameters](../DafnyRef/DafnyRef#sec-type-parameters), 
indicated in parentheses after the type name, state properties of the otherwise uninterpreted or opaque type.
The currently defined type parameters are designated by `==` (equality-supporting), `0` (auto-initializable), `00` (non-empty), and `!new` (non-reference).

## **Error: illegal type characteristic: '_token_' should be one of == or 0 or 00 or !new** {#p_illegal_type_characteristic}

```dafny
type T(X)
```

[Type parameters](../DafnyRef/DafnyRef#sec-type-parameters), 
indicated in parentheses after the type name, state properties of the otherwise uninterpreted or opaque type.
The currently defined type parameters are designated by `==` (equality-supporting), `0` (auto-initializable), `00` (non-empty), and `!new` (non-reference).

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

## **Error: constructors are allowed only in classes** {#p_constructor_in_class}

```dafny
module M {
  constructor M() {}
}
```

Constructors are methods that initialize class instances. That is, when a new instance of a class is being created, 
using the `new` object syntax, some constructor of the class is called, perhaps a default anonymous one.
So constructor declarations only make sense within classes.

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
const a: object;
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
const s := seq<int,int>(3, i=>i+1)
```

A `seq` type has one type parameter, namely the type of the elements of the sequence.
The error message states that the parser sees some number of type parameters different than one.
The type parameters are listed in a comma-separated list between `<` and `>`, after the type name.

<!-- There are two instances of this error. -->

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

## **Error: arrow-type arguments may not be declared as 'ghost'**

```dafny
const f: (ghost int, bool) -> int
```

[Arrow types](../DafnyRef/DafnyRef#sec-arrow-types) are the types of functions in Dafny.
They are designated with the arrow syntax, as shown in the example,
except that the types used cannot be declared as ghost.



## **Error: a 'by method' implementation is not allowed on a twostate _what_**

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

## **Error: a 'by method' implementation is not allowed on an extreme predicate**

```dafny
least predicate g() { 42 } by method { return 42; }
```

Least and greatest predicates are always ghost and do not have a compiled representation, 
so it makes no sense to have a `by method` alternative implementation.


## **Error: to use a 'by method' implementation with a _what_, declare _id_ using _what_, not '_what_ method'**

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


## **Error: a _adjective_ _what_ is supported only as ghost, not as a compiled _what_**

```dafny
twostate function method m(): int {
  42
}
```

The `twostate`, `least`, and `greatest` functions and predicates are always ghost and cannot be compiled, so they cannot be
declared as a `function method` (v3 only).


## **Error: a _what_ is always ghost and is declared with '_what_'**

```dafny
module {:options "--function-syntax:experimentalPredicateAlwaysGhost"} M {
  predicate method p() { true }
}
```

This error only occurs when the `experimentalPredicateAlwaysGhost` option is chosen.
It indicates that `predicates` are always ghost and cannot be declared with the (Dafny 3) syntax `predicate method`.
- If you intend to predicate to be ghost, remove `method`.
- If you intend the predicate to be non-ghost, you either cannot use `experimentalPredicateAlwaysGhost` or you should use `function` with a `bool` return type instead of `predicate`

## **Error: the phrase '_what_ method' is not allowed when using --function-syntax:4; to declare a compiled function, use just 'function'** {#p_deprecating_function_method}

```dafny
module {:options "--function-syntax:4"} M {
  function method f(): int { 42 }
}
```

In Dafny 4 on, the phrases `function method` and `predicate method` are no
longer accepted. Use `function` for compiled, non-ghost functions and
`ghost function` for non-compiled, ghost functions, and similarly for predicates.
See [the documentation here](../DafnyRef/DafnyRef#sec-function-syntax).

## **Error: there is no such thing as a 'ghost _what_ method'**

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

## **Error: a _what_ must be declared as either 'ghost _what_' or '_what_ method' when using --function-syntax:migration3to4**
```dafny
module {:options "--function-syntax:migration3to4"} M {
  function f(): int { 42 }
}
```

This error occurs only when using `migration3to4`. With this option, ghost functions are declared using `ghost function` and compiled functions using `function method`.
Change `function` in the declaration to one of these.

## **Error: 'decreases' clauses are meaningless for least and greatest predicates, so they are not allowed**

```dafny
least predicate m(i: int)
  decreases i
{
  true
}
```

Least and greatest predicates are not checked for termination. In fact, unbounded recursion is part of being coinductive.
Hence `decreases` clauses are inappropriate and not allowed.

## **Error: _name_ return type should be bool, got _type_**

```dafny
predicate b(): (r: boolean) { 4 }
```

A predicate is a function that returns `bool`. The return type here is something else.
If you mean to have a non-`bool` return type, use `function` instead of `predicate`.

## **Error: _name_s do not have an explicitly declared return type; it is always bool. Unless you want to name the result: ': (result: bool)'**

```dafny
predicate p(): bool { true } 
```

A `predicate` is simply a `function` that returns a `bool` value.
Accordingly, the type is (required to be) omitted, unless the result is being named.
So `predicate p(): (res: bool) { true }` is permitted

## **Error: A '*' expression is not allowed here**

```dafny
function m(i: int): int
  decreases *
{
  42
}
```

A method or loop with a `decreases *` clause is not checked for termination.
This is only permitted for non-ghost methods and loops.


## **Error: A '*' frame expression is not permitted here**

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

## **Error: invalid statement beginning here (is a 'label' keyword missing? or a 'const' or 'var' keyword?)**

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

## **Error: An initializing element display is allowed only for 1-dimensional arrays**

```dafny
method m() {
  var a := new int[2,2] [1,2,3,4];
}
```

One-dimensional arrays can be initiallized like `var s := new int[][1,2,3,4];`,
but multi-dimensional arrays cannot. The alternatives are to initialize the array
in a loop after it is allocated, or to initialize with a function, as in
`var a:= new int[2,2]((i: int, j: int)=>i+j)`.

## **Error: a local variable should be initialized using ':=', ':-', or ':|', not '='**

```dafny
method m() {
  var x = 5;
}
```

Local variables are initialized with `:=` (and sometimes with `:-` or `:|`), but not with `=`.
In Dafny `=` is used only in type definitions.

## **Error: LHS of assign-such-that expression must be variables, not general patterns**

```dafny
datatype D = D(x: int, y: int)
method m() {
  var D(x,y) :| x + y == 5;
}
```

The `:|` syntax is called _assign-such-that_: the variables on the left-hand-side are initiallized or assigned
some non-deterministic values that satisfy the predicate on the right-hand-side.

However, Dafny only allows a list of simple variables on the left, not datatype deconstructor patterns, as seen here.


## **Error: 'modifies' clauses are not allowed on refining loops**

_Refining statements, including loops, are deprecated._


## **Error: Expected 'to' or 'downto'**

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
```dafny
method m() {
  var to: int := 6;
  var downto: int := 8;
  for to := to to downto {}
}
```
is legal, but not at all recommended.


## **Error: A 'decreases' clause that contains '*' is not allowed to contain any other expressions**

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

## **Error: a forall statement with an ensures clause must have a body**

<!-- TODO: This example does not yet work in the new CLI because there is no way to turn on /noCheating in the new CLI -->

<!-- %check-legacy %options -compile:0 -noCheating:1 -->
```dafny
module  M {
  predicate f(i: int) { true }
  method  m(a: seq<int>) {
    forall i | 0 <= i < 10
       ensures f(i)
  }
}
```

A forall statement without a body is like an assume statement: the ensures clause is assumed in the following code.
Assumptions like that are a risk to soundness because there is no check that the assumption is true.
Thus in a context in which open assumptions are not allowed, body-less forall statements are also not allowed.


## **Error: the main operator of a calculation must be transitive**

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


## **Error: this operator cannot continue this calculation**

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

## **Error: a calculation cannot end with an operator**

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

## **Error: Ambiguous use of ==> and <==. Use parentheses to disambiguate.**

```dafny
const b := true ==> false <== true;
```

The `==>` and `<==` operators have the same precedence but do not associate with each other.
You must use parentheses to show how they are grouped. Write the above example as either
`(true ==> false) <== true` or `true ==> (false <== true)`.

In contrast, `p ==> q ==> r` is `p ==> (q ==> r)` and
`p <== q <== r` is `(p <== q) <== r`.

See [this section](../DafnyRef/DafnyRef#sec-implication-and-reverse-implication) for more information.

<!-- There are two instances of this error, one in which the first operator is ==> and one in which it is <== -->

## **Error: Ambiguous use of && and ||. Use parentheses to disambiguate.**

```dafny
const b := true && false || true
```

The `&&` and `||` operators have the same precedence but do not associate with each other.
You must use parentheses to show how they are grouped. Write the above example as either
`(true && false) || true` or `true && (false || true)`.

## **Error: chaining not allowed from the previous operator**

```dafny
const c := 1 in {1} == true
```

[Chained operations](../DafnyRef/DafnyRef#sec-basic-types)
are a sequence of binary operations without parentheses: _a op b op c op d op e_.
But there are limitations on which operators can be in one chain together.

In particular, the relational operators `in` and `!in` may not be part of a chain.
Use parentheses as necessary to group the operations.

## **Error: a chain cannot have more than one != operator**

```dafny
const c := 1 != 2 != 3
```

[Chained operations](../DafnyRef/DafnyRef#sec-basic-types)
are a sequence of binary operations without parentheses: _a op b op c op d op e_.
But there are limitations on which operators can be in one chain together.

In particular for this error message, one cannot have chains that include more than one `!=` operator.

## **Error: this operator chain cannot continue with an ascending operator**

```dafny
const c := 4 > 3 < 2
```

[Chained operations](../DafnyRef/DafnyRef#sec-basic-types)
are a sequence of binary operations without parentheses: _a op b op c op d op e_.
But there are limitations on which operators can be in one chain together.

In particular for this error message, one cannot have chains that include both
less-than operations (either `<` or `<=`) and greater-than operations (either `>` or `>=`).


## **Error: this operator chain cannot continue with a descending operator**

```dafny
const c := 2 < 3 > 4
```

[Chained operations](../DafnyRef/DafnyRef#sec-basic-types)
are a sequence of binary operations without parentheses: _a op b op c op d op e_.
But there are limitations on which operators can be in one chain together.

In particular for this error message, one cannot have chains that include both
less-than operations (either `<` or `<=`) and greater-than operations (either `>` or `>=`).

## **Error: can only chain disjoint (!!) with itself**

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

## **Error: this operator cannot be part of a chain**

```dafny
const c := 2 < 3 in 4
```

The operators `in` and `!in` are relational operators, but they may not occur in a chain.
Use parentheses if necessary. An expression like the above is not type-correct in any case.

## **Error: invalid relational operator**

```dafny
const s : set<int>
const r := s ! s
```

The parser is expecting a relational expression, that is, two expressions separated by a relational operator
(one of `==`, `!=`, `>`, `>=`, `<`, `<=`, `!!`, `in`, `!in`). But the parser saw just a `!` ,
which could be the beginning of `!=`, `!!`, or `!in`, but is not continued as such.
So perhaps there is extraneous white space or something else entirely is intended.

## **Error: invalid relational operator (perhaps you intended \"!!\" with no intervening whitespace?)**

```dafny
const s : set<int>
const r := s ! ! s
```

The parser is expecting a relational expression, that is, two expressions separated by a relational operator
(one of `==`, `!=`, `>`, `>=`, `<`, `<=`, `!!`, `in`, `!in`). But the parser saw two `!` separated by
white space. This is possibly meant to be a `!!` operator, but it could also just be an illegal expression.

## **Error: Ambiguous use of &, |, ^. Use parentheses to disambiguate.**

```dafny
const i: int := 5 | 6 & 7
```

The bit-operators `&`, `|`, and `^` have the same precedence but do not associate with each other.
So if they are used within the same expression, parentheses have to be used to show how they
are grouped. The above example should be written as either `(5 | 6) & 7` or `5 | (6 & 7)`.

## **Error: too many characters in character literal**

<!-- %check-resolve --unicode-char:false -->
```dafny
const c := '🚀';
```

A character literal can only contain a single value of the built-in char type.
When --unicode-char is disabled, the char type represents UTF-16 code units, 
so this means a character literal can only contain a character that can be represented
with a single such unit, i.e. characters in the Basic Multilingual Plane. 
The rocket ship emoji above, however, is encoded with two surrogate code points.

This can be fixed by enabling the --unicode-char mode, as that defines char as any
Unicode scalar value, but be aware that it may change the meaning of your program.

More detail is given [here](../DafnyRef/DafnyRef#sec-character-constant-token) and [here](../DafnyRef/DafnyRef#sec-escaped-characters).;

## **Error: binding not allowed in parenthesized expression**

```dafny
method m() {
  var c := ( 4 := 5 );
}
```

A binding of the form `x := y` is used in map-display expresions, in which case they are enclosed in square brackets,
not parentheses. The above example should be `var c := [ 4 := 5 ]`

## **Error: A forming expression must be a multiset**

A set/iset/multiset display expression can have two forms. 
One form is a list of values enclosed by curly braces: `var c := multiset{1,2,2,3}`.
The other appears as a conversion operation: `var c := multiset(s)`.
However, this second form can only be used to convert a set to a multiset.

In the current parser, however, this error message is unreachable.
The tests that check for this error case are already known to be false by previous testing.

## **Error: a map comprehension with more than one bound variable must have a term expression of the form 'Expr := Expr'**

```dafny
const s := map x, y  | 0 <= x < y < 10 :: x*y
```

A map comprehension defines a map, which associates a value with each member of a set of keys.
The full syntax for a map comprehension looks like `map x | 0 <= x < 5:: x*2 => x*3`
which maps the keys `0, 2, 4, 6, 8` to the values `0, 3, 6, 9, 12` respectively.

One can abbreviate the above syntax to expressions like `map x | 0 <= x < 5 :: x*3`,
which is equivalent to `map x | 0 <= x < 5 :: x => x*3`. The missing expression before
the `=>` is just the declared identifier.

One can also have multiple variables involved as in `map x, y | 0 < x < y < < 5 :: 10*x+y => 10*y+x`,
which defines the mappings `(12=>21, 13=>31, 14=>41, 23=>32, 24=>42, 34=>43)`.

But when there are multiple variables, one cannot abbreviate the `=>` syntax with just its right-hand expression,
becuase it is not clear what the left-hand expression should be. 

Rewrite the failing example above as `const s := map x, y  | 0 <= x < y < 10 :: f(x,y) => x*y` for some `f(x,y)` that gives
a unique value for each pair of `x,y` permitted by the range expression (here `0 <= x < y < 10 `).

## **Error: a variable in a let expression should be initialized using ':=', ':-', or ':|', not '='**

```dafny
method m() {
  var x := var y = 5; y*y;
}
```

Like local variables, let variables are initialized with `:=` (and sometimes with `:-` or `:|`), but not with `=`.
In Dafny `=` is used only in type definitions.

## **Error: LHS of let-such-that expression must be variables, not general patterns**

```dafny
datatype Data = D(i: int, j: int)
const c: int := var Data(d,dd) :| d == 10 && dd == 11; d
```

The let-such-that expression initializes a variable to some value satisfying a given condition.
For example, one might write `const cc := var x: int :| x <= 10; x`,
where `cc` would get some value `x` satisfying `x < 10`.

For simplicity, however, Dafny requires the variables being initialized to be simple names, not patterns.

## **Error: ':-' can have at most one left-hand side**

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
  var rr, rrr :- m(), 44; Outcome.Success(1) 
}
```

Within a function, the `:-` operator is limited to a most one left-hand-side and exactly one-right-hand-side.

## **Error: ':-' must have exactly one right-hand side**

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
and in the context of a let-or-fail expression, as in the body of `test()` in the example above.

In contrast to the let expression (`:=`), which allows multiple parallel initializations, the let-or-fail expression (`:-`) is implemented to
only allow at most a single left-hand-side and a single-right-hand-side.



## **Error: a set comprehension with more than one bound variable must have a term expression**

```dafny
const s := set x, y  | 0 <= x < y < 10 
```

A set comprehension (1) declares one or more variables, (2) possibly states some limits on those variables, 
and (3) states an expression over those variables that are the values in the set.

If there is no expression, then the expression is taken to be just the _one_ declared variable.
For instance one could write `set b: bool`, which is equivalent to `set b: bool :: b` and would be the set of all `bool` values.
Another example is `set x: nat | x < 5, which is equivalent to `set x: nat | x < 5:: x` and would be the set `{0, 1, 2, 3, 4}`.

But if more than one variable is declared, then there is no natural implicit expression to fill in after the `::` if it is omitted, 
so some expression is required. The failing example above, for example, might use the expression `x * y`, as in 
`set x, y  | 0 <= x < y < 10 :: x * y`, or any other expression over `x` and `y`.


## **Error: invalid name after a '.'**

This error message is not reachable in current Dafny.
If it occurs, please report an internal bug (or obsolete documentation).


## **Error: incorrectly formatted number**

This error can only result from an internal bug in the Dafny parser.
The parser recognizes a legitimate sequence of digits or sequence of hexdigits or
a decimal number and then passes that string to a libary routine to create a BigInteger
or BigDecimal. Given the parser logic, that parsing should never fail.

<!-- There are three instances of this message, one for digits one for hexdigits, one for decimaldigits -->

<!-- Scanner.frame -->

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
scanner recopgnizes. The only pragma ever recognized was `#line`.

