
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

## XError: type-parameter variance is not allowed to be specified in this context

```dafny
type List<T>
method m<T>(i: int, list: List<T>) {}
```

TODO - not yet working
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

## Error: a 'by method' implementation is not allowed on a twostate _what_

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

Two state functions and  predicates are always ghost and do not have a compiled representation.
Such functions use values from two different program (heap) states, which is not 
something that can be implemented (at least with any degree of good performance) in conventional programming languages.

Because there is no feasible compiled verion of a two-state function, it cannot have a `by method` block (which is always compiled).

## Error: a 'by method' implementation is not allowed on an extreme predicate

```dafny
least predicate g() { 42 } by method { return 42; }
```

Least and greatest predicates are always ghost and do not have a compiled representation, 
so it makes no sense to have a `by method` alternative implementation.


## Error: to use a 'by method' implementation with a {what}, declare '{id.val}' using '{what}', not '{what} method'

TODO

## Error: a {adjective} {what} is supported only as ghost, not as a compiled {what}

TODO

## Error: a {what} is always ghost and is declared with '{what}'

Prior to Dafny 4, a 
TODO

## Error: the phrase '_what_ method' is not allowed; to declare a compiled _what_, use just '_what_'

```dafny
module {:options "--function-syntax:4"} M {
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

```dafny
module M {
  constructor M() {}
}
```

Constructors are methods that initialize classe instances. That is, when a new instance of a class is being created, 
using the `new` object syntax, then some constructor of the class is called, perhaps a default anonymous one.
So constructor declarations only make sense within classes.

## Error: a method must be given a name (expecting identifier)

```dafny
method {:extern "M"} (i: int) {}
```

A method declaration always requires an identifier between the `mehtod` keyword and the `(` that starts the formal parameter list.
This is the case even when, as in the example above, a name is specified using `:extern`. The extern name is only used in the
compiled code; it is not the name used to refer to the method in Dafny code

## Error: type of _k can only be specified for least and greatest lemmas

TODO

## Error: constructors cannot have out-parameters

```dafny
class C {
  constructor (i: int) returns (j: int) {}
}
```

Constructors are used to initalize the state of an instance of a class.
Thus they typically set the values of the fields of the class instance.
Constructors are used in `new` object expressions, which return 
a reference to the newly constructed object (as in `new C(42)`).
There is no syntax to receive out-parameter values of a contructor
and they may not be declared. 
(This is similar to constructors in other progrmaming languages, like Java.)


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

## XError: use of the 'nameonly' modifier must be accompanied with a parameter name

```dafny
method m(i: int, nameonly : int) {}
```

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

TODO: If this can happen at all it is with an unusual unicode char

A character literal consists of two `'` characters enclosing either
- a single ASCII character (that is not a backslash)
- a backslash-escaped character
- a sequence of characters designating a unicode character

More detail is given [here](../DafnyRef/DafnyRef#sec-character-constant-token) and [here](../DafnyRef/DafnyRef#sec-escaped-characters).;

## Error: binding not allowed in parenthesized expression

TODO

## Error: incorrectly formatted number

This error can only result from an internal bug in the Dafny parser.
The parser should recognize a legitimate sequence of digits or sequence of hexdigits or
a decimal number and then pass that string to a libary routine to create a BigInteger
or BigDecimal. Given the parser logic, that parsing should never fail.

## Error: a map comprehension with more than one bound variable must have a term expression of the form 'Expr := Expr'

```dafny
const s := map x, y  | 0 <= x < y < 10 :: x*y
```

A map comprehension defines a map, which associates a value with each member of a set of keys.
The full syntax for a map comprehension looks like `map x | 0 <= x < 5:: x*2 => x*3`
which maps the keys `0, 2, 4, 6, 8` to the values `0, 3, 6, 9, 12` respectively.

One can abbreviate the above syntax to expressions like `map x | 0 <= x < 5 :: x*3`,
which is equivalent to `map x | 0 <= x < 5 :: x => x*3`.

One can also have multiple variables involved as in `map x, y | 0 < x < y < < 5 :: 10*x+y => 10*y+x`,
which defines the mappings `(12 => 21, 13=>31, 14=>41, 23=>32, 24=>42, 34=>43)`.

But when there are multiple variables, one cannot abbreviate the `=>` syntax with just itts right-hand expression,
becuase it is not clear what the left-hand expression should be. If there is just one variable, say `x`, then the 
default left hand expression is just `x`. 

The failing example above as `const s := map x, y  | 0 <= x < y < 10 :: f(x,y) => x*y` for some `f(x,y)` that gives
a unique value for each pair of `x,y` permitted by the range expression (here `0 <= x < y < 10 `).

## Error: a set comprehension with more than one bound variable must have a term expression

```dafny
const s := set x, y  | 0 <= x < y < 10 
```

A set comprehension (1) declares one or more variables, (2) possibly states some limits on those variables, 
and (3) states an expression over those variables that are the values in the set.

If there is no expression, then the expression is taken to be just the _one_ declared variable.
For instance one could write `set b: bool`, which is equivalent to `set b: bool :: b` and would be the set of all `bool` values.
Another example is `set x: nat | x < 5, which is equivalent to `set x: nat | x < 5:: x` and would be the set `{0, 1, 2, 3, 4}`.

But if more than one variable is declared, then there is no natural implicit expression to fill in if it is omitted, 
so such an expression is required. The failing example above, for example, might use the expression `x * y`, as in 
`set x, y  | 0 <= x < y < 10 :: x * y`, or any other expression over `x` and `y`.

## Error: LHS of let-such-that expression must be variables, not general patterns

```dafny
datatype Data = D(i: int, j: int)
const c: int := var Data(d,dd) :| d == 10 && dd == 11; d
```

The let-such-that expression initializes a variable to some value satisfying a given condition.
For example, one might write `const cc := var x: int :| x <= 10; x`,
where `cc` would get some value `x` satisfying `x < 10`.

For simplicity, however, Dafny requires the variables being initialized to be simple names, not patterns.

## Error: ':-' can have at most one left-hand side

```dafny
datatype Outcome<T> = 
  | Success(value: T) 
  | Failure(error: string) 
{ predicate method IsFailure() { this.Failure? } 
  function method PropagateFailure<U>(): Outcome<U> 
    requires IsFailure() 
  { Outcome<U>.Failure(this.error) // this is Outcome<U>.Failure(...) 
  }
 
  function method Extract(): T requires !IsFailure() { this.value } 
}

function m(): Outcome<int> { Outcome<int>.Success(0) }
function test(): Outcome<int> {
  var rr, rrr :- m(), 44; Outcome.Success(1) 
}
```


## Error: ':-' must have exactly one right-hand side

```dafny
datatype Outcome<T> = 
  | Success(value: T) 
  | Failure(error: string) 
{ predicate method IsFailure() { this.Failure? } 
  function method PropagateFailure<U>(): Outcome<U> 
    requires IsFailure() 
  { Outcome<U>.Failure(this.error) // this is Outcome<U>.Failure(...) 
  }
 
  function method Extract(): T requires !IsFailure() { this.value } 
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
only allow a single left-hand-side and a single-right-hand-side.


## Error: invalid DotSuffix

TODO _ IMPROVE






