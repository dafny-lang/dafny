
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
fields, constants, methods, and functions within classes.

## Error: argument to :options attribute must be a literal string

```dafny
module N { const opt := "--function-syntax:4" }
import opened N
module {:options opt} M{}
```

The value of an options attribute cannot be a computed expression. It has top be a literal string.

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
```

## Error: expected either a '{' or a 'refines' keyword here, found _token_

```dafny
module M {}
module N refine M {}
```

The [syntax for a module declaration](../DafnyRef/DafnyRef#sec-modules) is either `module M { ... }` or
`module M refines N { ... }` with optional attributes after the `module` keyword.
This error message often occurs if the `refines` keyword is misspelled.
