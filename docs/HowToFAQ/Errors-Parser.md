
## Error: Duplicate declaration modifier: abstract

```dafny
abstract abstract module M {}
```

No Dafny modifier, such as [`abstract`, `static`, `ghost`](../DafnyRef/DafnyRef#sec-declaration-modifiers) may be repeated. Such repetition would be superfluous even if allowed.

## Error: a _decl_ cannot be declared 'abstract'
 
```dafny
module M {
  abstract const c := 4
}
```

Only some kinds of declarations can be declared abstract. In the example,
a const declaration cannot be abstract.

## Error: a function-by-method has a ghost function body and a non-ghost method body; a function-by-method declaration does not use the 'ghost' keyword.

```dafny
ghost function f(): int
{
  42
} by method {
  return 42;
}
```

Functions with a [by method](../DafnyRef/DafnyRef#sec-function-declarations)
section to their body can be used both in ghost contexts and in non-ghost contexts; in ghost contexts the function body is used and in compiled contexts
the by-method body is used. The `ghost` keyword is not permitted on the 
declaration.

## Error: _decl_ cannot be declared 'ghost' (it is 'ghost' by default)

```dafny
ghost function f(): int { 42 }
```

For versions prior to Dafny 4, the `function` keyword meant a ghost function
and `function method` meant a non-ghost function. 
From Dafny 4 on, `ghost function` means a ghost function and 
`function` means a non-ghost function. 
See the discussion [here](../DafnyRef/DafnyRef#sec-function-syntax) for
a discussion of options to control this feature.

## Error: a _decl_ cannot be declared 'ghost'

```dafny
ghost module M {}
```

Only some kinds of declarations can be declared `ghost`, most often functions,
fields, and local declarations. In the example, a `module` may not be `ghost`.

## Error: a _decl_ cannot be declared 'static'

```dafny
static module M {}
```

Only some kinds of declarations can be declared 'static', most often 
fields, constants, methods, and functions, and only within classes.

## Error: argument to :options attribute must be a literal string

```dafny
module N { const opt := "--function-syntax:4" }
import opened N
module {:options opt} M{}
```

The value of an options attribute cannot be a computed expression. It must be a literal string.

## Error: sorry, bitvectors that wide (_number_) are not supported

```dafny
const b: bv2147483648
```

A bitvector type name is the characters 'bv' followed by a non-negative
integer literal. However, dafny only supports widths up to the largest
signed 32-bit integer (2147483647).

## Error: sorry, arrays of that many dimensions (_number_) are not supported

```dafny
const a: array2147483648<int>
```

A multi-dimensional array type name is the characters 'array' followed by
a positive integer literal. However, dafny only supports numbers of 
dimensions up to the largest signed 32-bit integer (2147483647).
In practice (as of v3.9.1) dimensions of more than a few can take 
overly long to resolve ([Issue #3180](https://github.com/dafny-lang/dafny/issues/3180)).

## Error: cannot declare identifier beginning with underscore

```dafny
const _myconst := 5
```

Identifiers beginning with underscores are reserved for internal use.
A single-character underscore as a variable is permitted in matching expressions and statements as a wild identifier.

## Error: There is no point to an export declaration at the top level

```dafny
export M
method M() {}
```

Although all top-level declarations are contained in an implicit top-level module, there is no syntax to import that module. Such an import would likely cause
a ciruclar module dependency error. If the module cannot be imported, there is no point to any export declarations.

## Error: Refinement cannot change the constructors of a `datatype`.  To refine _id_, either omit this `...` or omit the `=` sign and the datatype constructors.

```dafny
abstract module M { datatype D = A | B }
module N refines M { datatype D = ... Y | Z }
```

There are limitations on refining a datatype, namely that the set of constructors cannot be changed.

## Error: Refinement cannot change the base type of a `newtype`.  To refine _id_, either omit this `...` or omit the `=` sign and the parent type's body.

```dafny
abstract module M { newtype T = int }
module N refines M { newtype T = ... int }
```

There are limitations on refining a newtype, namely that the base type cannot be changed. You can change an opaque type into a newtype, however.

## Error: iterators don't have a 'returns' clause; did you mean 'yields'?

```dafny
iterator Count {
  TODO
}
```

## Error: fields are not allowed to be declared at the module level; instead, wrap the field in a 'class' declaration

```dafny
var c := 5
```

## Error: expected either a '{' or a 'refines' keyword here, found _token_

```dafny
module M {}
module N refine M {}
```

The [syntax for a module declaration](../DafnyRef/DafnyRef#sec-modules) is either `module M { ... }` or
`module M refines N { ... }` with optional attributes after the `module` keyword.
This error message often occurs if the `refines` keyword is misspelled.

## Error: cannot declare identifier beginning with underscore
TODO  - this message found earlier also

```dafny
const _special := 6
```

User-declared identifiers may not begin with an underscore; such identifiers
are reserved for internal use. 
In match statements and expressions, an 
identifier that is a single underscore is used as a wild-card match.

## Error: type-parameter variance is not allowed to be specified in this context

```dafny
```

TODO - 2 instances

## Error: mutable fields are not allowed in value types

```dafny
datatype D = A | B  { var c: D }
```

The `var` declaration declares a mutable field, which is only permitted within
classes, traits and iterators. All members of value-types, such as datatypes,
are constants (declared with `const`).

## Error: a const declaration must have a type or a RHS value

```dafny
const i
```

A `const` declaration needs its type indicated by either an explicit type
or a right-hand-side expression, whose type is then the type of the 
declared identifier. So use syntax either like `const i: int` or `const i:= 5`
(or both together).

## Error: a 'by method' implementation is not allowed on a twostate {what}

TODO

## Error: a 'by method' implementation is not allowed on an extreme predicate

TODO

## Error: to use a 'by method' implementation with a {what}, declare '{id.val}' using '{what}', not '{what} method'

TODO

## Error: a {adjective} {what} is supported only as ghost, not as a compiled {what}

TODO

## Error: a {what} is always ghost and is declared with '{what}'

Prior to Dafny 4, a 
TODO

## Error: the phrase '_what_ method' is not allowed; to declare a compiled _what_, use just '_what_'

```dafny
module {:options "-functionSyntax:4"} M {
  function method f(): int { 42 }
}
```

In Dafny v4 on, the phrases `function method` and `predicate method` are no
longer accepted. Use `function` for compiled, non-ghost functions and
`ghost function` for non-compiled, ghost functions, and similarly for predicates.

See [the documentation here](../DafnyRef/DafnyRef#sec-function-syntax).

## Error: there is no such thing as a 'ghost _what_ method'

```dafny
module {:options "-functionSyntax:experimentalDefaultGhost"} M {
  ghost function method f(): int { 42 }
}
```

Pre-Dafny 4, a `function method` and a `predicate method` are explicitly
non-ghost, compiled functions, and therefore cannot be declared `ghost` as well.If indeed the function or predicate is intended to be ghost, leave out `method`; if it is intended to be non-ghost, leave out `ghost`.

From Dafny 4 on, a ghost function is declared `ghost function` and a non-ghost function is declared `function` and there is no longer any declaration of the form `function method`, and similarly for predicates. 

See [the documentation here](../DafnyRef/DafnyRef#sec-function-syntax).

## Error: a {what} must be declared as either 'ghost {what}' or '{what} method'

TODO

## Error: formal cannot be declared 'ghost' in this context

TODO
IMPROVE

## Error: constructors are allowed only in classes

TODO

## Error: a method must be given a name (expecting identifier)

TODO

## Error: type of _k can only be specified for least and greatest lemmas

TODO

## Error: constructors cannot have out-parameters

TODO

## Error: formal cannot be declared 'ghost' in this context

TODO

## Error: formal cannot be declared 'new' in this context

TODO

## Error: formal cannot be declared 'nameonly' in this context

TODO

## Error: formal cannot be declared 'older' in this context

TODO

## Error: invalid formal-parameter name in datatype constructor

TODO

## Error: use of the 'nameonly' modifier must be accompanied with a parameter name

TODO

## Error: set type expects only one type argument

TODOa - 2 instances

## ERROR: multiset type expects only one type argument

TODO

## Error: seq type expects only one type argument

TODO -- also in a disolay expresion

## Error: map type expects two type arguments

TODO

## Error: imap type expects two type arguments

TODO

## Error: arrow-type arguments may not be declared as 'ghost'

TODO

## Error: out-parameters cannot have default-value expressions

TODO

## Error: unexpected type parameter option - should be == or 0 or !new

TODO

## Error: A 'decreases' clause that contains '*' is not allowed to contain any other expressions

TODO

## Error: A 'reads' clause that contains '*' is not allowed to contain any other expressions

TODO

## Error: A '*' frame expression is not permitted here

TODO

## Error: {name} return type should be bool, got {ty}

TODO

## Error: {name}s do not have an explicitly declared return type; it is always bool. Unless you want to name the result: ': (result: bool)'

TODO

## Error: 'decreases' clauses are meaningless for least and greatest predicates, so they are not allowed

TODO

## Error: A '*' expression is not allowed here

TODO

## Error: invalid statement (did you forget the 'label' keyword?)

TODO

## Error: LHS of assign-such-that expression must be variables, not general patterns

TODO

## Error: 'modifies' clauses are not allowed on refining loops

TODO - deprecated?

## Error: the main operator of a calculation must be transitive

TODO

## Error: this operator cannot continue this calculation

TODO

## Error: a calculation cannot end with an operator

TODO

## Error: a forall statement with an ensures clause must have a body

TODO

## Error: An initializing element display is allowed only for 1-dimensional arrays

TODO

## Error: Expected 'to' or 'downto'

TODO

## Error: Ambiguous use of ==> and <==. Use parentheses to disambiguate.

TODO -- 2 instances

## Error: Ambiguous use of && and ||. Use parentheses to disambiguate.

TODOa -- 4 instances

## Error: chaining not allowed from the previous operator

TODO

## Error: a chain cannot have more than one != operator

TODO

## Error: this operator chain cannot continue with an ascending operator

TODO

## Error: this operator chain cannot continue with a descending operator

TODO

## Error: can only chain disjoint (!!) with itself

TODO

## Error: this operator cannot be part of a chain

TODO

## Error: invalid RelOp

TODO - IMPROVE

## Error: invalid RelOp (perhaps you intended \"!!\" with no intervening whitespace?)

TODO - IMPROVE

## Error: Ambiguous use of &, |, ^. Use parentheses to disambiguate.

TODO - IMPROVE -- 3 instances

## Error: A forming expression must be a multiset

 TODO

## Error: too many characters in character literal

TODO

## Error: binding not allowed in parenthesized expression

TODO

## Error: incorrectly formatted number

TODO -- 3 instances

## Error: a map comprehension with more than one bound variable must have a term expression of the form 'Expr := Expr'

TODO

## Error: a set comprehension with more than one bound variable must have a term expression

TODO

## Error: LHS of let-such-that expression must be variables, not general patterns

TODO

## Error: ':-' can have at most one left-hand side

TODO - since when?

## Error: ':-' must have exactly one right-hand side

TODO

## Error: invalid DotSuffix

TODO _ IMPROVE






