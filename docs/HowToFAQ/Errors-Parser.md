<!-- %check-resolve %default -->

<!-- Parser.cs, but not Deprecated warnings or syntactic errors -->

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
iterator Count(n: nat) returns (x: nat) {
  var i := 0;
  while i < n {
    x := i;
    yield;
    i := i + 1;
  }
}
```

An iterator is like a co-routine: its control flow produces (yields) a value, but the execution continues from that point (a yield statement) to go on to produce the next value, rather than exiting the method. 
To accentuate this difference, a `yield` statement is used to say when the next value of the iterator is ready, rather than a `return` statement.
In addition, the declaration does not use `returns` to state the out-parameter, as a method would. Rather it has a `yields` clause
The example above is a valid example if `returns` is replaced by `yields`.

## Error: fields are not allowed to be declared at the module level; instead, wrap the field in a 'class' declaration

```dafny
var c: int
```

`var` declarations are used to declare fields of classes, local variables in method bodies, and identifiers in let-expressions.
But mutable field declarations are not permitted at the static module level, including in the (unnamed) toplevel module.
Rather, you may want the declaration to be a `const` declaration or you may want the mutable field to be declared in the body of a class.

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


## Error: to use a 'by method' implementation with a _what_, declare _id_ using _what_, not '_what_ method'

```dafny
function method m(): int {
  42
} by method {
  return 42;
}
```

`by method` constructs copmbine a ghost function (or predicate) with a non-ghost method.
The two parts ciompute the same result, and are verified to do so.
Uses of the function are verified using the function body, but the method body is used when the function is compiled.

Thus the function part is always implicitly `ghost` and may not be explicitly declared `ghost`.

## Error: a _adjective_ _what_ is supported only as ghost, not as a compiled _what_

```dafny
twostate function method m(): int {
  42
}
```

The `twostate`, `least`, and `greatest` functions and predicates are always ghost and cannot be compiled, so they cannot be
declared as a `function method` (v3 only).


## Error: a _what_ is always ghost and is declared with '_what_'

```dafny
x
```
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

## Error: a _what_ must be declared as either 'ghost _what_' or '_what_ method'

```dafny
x
```
TODO

## Error: formal cannot be declared 'ghost' in this context

```dafny
function m(ghost i: int): int {
  42
}
```

If a method, function, or predicate is declared as ghost, then its formal parameters may not also be declared ghost.
Any use of this construct will always be in ghost contexts.

## Error: constructors are allowed only in classes

```dafny
module M {
  constructor M() {}
}
```

Constructors are methods that initialize class instances. That is, when a new instance of a class is being created, 
using the `new` object syntax, then some constructor of the class is called, perhaps a default anonymous one.
So constructor declarations only make sense within classes.

## Error: a method must be given a name (expecting identifier)

```dafny
method {:extern "M"} (i: int) {}
```

A method declaration always requires an identifier between the `mehtod` keyword and the `(` that starts the formal parameter list.
This is the case even when, as in the example above, a name is specified using `:extern`. The extern name is only used in the
compiled code; it is not the name used to refer to the method in Dafny code

## XError: type of _k_ can only be specified for least and greatest lemmas

```dafny
least predicate b[nat](i: int) { true }
```

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


## XError: formal cannot be declared 'ghost' in this context

```dafny
method m(i: int) returns (ghost r: int) {}
```
TODO - multiple instances

## Error: formal cannot be declared 'new' in this context

```dafny
method m(i: int) returns (new r: int) {}
```
TODO

## Error: formal cannot be declared 'nameonly' in this context

```dafny
method m(i: int) returns (nameonly r: int) {}
```
TODO

## Error: formal cannot be declared 'older' in this context

```dafny
method m(i: int) returns (older r: int) {}
```
TODO

## Error: invalid formal-parameter name in datatype constructor

```dafny
x
```
TODO

## XError: use of the 'nameonly' modifier must be accompanied with a parameter name

```dafny
method m(i: int, nameonly : int) {}
```

TODO

## Error: set type expects only one type argument

```dafny
const c: set<int,bool>
```

A `set` type has one type parameter, namely the type of the elements of the set.
The error message states that the parser sees some number of type parameters different than one.

TODOa - 2 instances

## Error: multiset type expects only one type argument

```dafny
const c: multiset<int,bool>
```

A `multiset` type has one type parameter, namely the type of the elements of the multiset.
The error message states that the parser sees some number of type parameters different than one.

## Error: seq type expects only one type argument

```dafny
const c: seq<int,bool>
```

A `seq` type has one type parameter, namely the type of the elements of the sequence.
The error message states that the parser sees some number of type parameters different than one.

TODO -- also in a display expresion

## Error: map type expects two type arguments

```dafny
const m: map<int,bool,string>
```

A `map` type has two type parameters: the type of the keys and the type of the values.
The error message states that the parser sees some number of type parameters different than two.


## Error: imap type expects two type arguments

```dafny
const m: imap<int,bool,string>
```

A `imap` type has two type parameters: the type of the keys and the type of the values.
The error message states that the parser sees some number of type parameters different than two.

## Error: arrow-type arguments may not be declared as 'ghost'

```dafny
x
```
TODO

## Error: out-parameters cannot have default-value expressions

```dafny
method m(i: int) returns (j: int := 0) { return 42; }
```

Out-parameters of a method are declared (inside the parentheses after the `returns` keyword)
with just an identifier and a type, separated by a colon. 
No initializing value may be given. If a default value is needed, assign the out-parameter
that value as a first statement in the body of the method.

## XError: unexpected type parameter option - should be == or 0 or !new

```dafny
type T(^)
```
TODO

## Error: A 'decreases' clause that contains '*' is not allowed to contain any other expressions

```dafny
x
```
TODO

## Error: A 'reads' clause that contains '*' is not allowed to contain any other expressions

```dafny
x
```
TODO

## Error: A '*' frame expression is not permitted here

```dafny
x
```
TODO

## XError: _name_ return type should be bool, got _type_

```dafny
predicate b(): int { 4 }
```

TODO

## Error: {name}s do not have an explicitly declared return type; it is always bool. Unless you want to name the result: ': (result: bool)'

```dafny
x
```
TODO

## XError: 'decreases' clauses are meaningless for least and greatest predicates, so they are not allowed

```dafny
least predicate m(i: int)
  decreases i
{
  true
}
```
TODO

## XError: A '*' expression is not allowed here

```dafny
const c := *
```


TODO

## Error: invalid statement beginning here (is a 'label' keyword missing? or a 'const' or 'var' keyword?)

```dafny
method m() {
  x: int := 5;
}
```

In this situation the parser sees the identifier (x) and the following colon.
This is not a legal start to a statement. Most commonly either
* a `var` or `const` keyword is missing, and the `x:` is the beginning of a declaration, or
* a `label` keyword is missing and the identifier is the name of the label for the statement that follows.
(The second error is somewhat common because in C/C++ and Java, there is no keyword introducing a label, just the identifier and the colon.)


## Error: LHS of assign-such-that expression must be variables, not general patterns

```dafny
x
```
TODO

## Error: 'modifies' clauses are not allowed on refining loops

```dafny
x
```
TODO - deprecated?

## Error: the main operator of a calculation must be transitive

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
This default operator is the implicit between each consaecutive pair of expressions
in the body of the calc statement.

But the operator has to be transitive: `!=` is not allowed; `==`, `<`, `<=`, '>' and '>=' asre allowed.


## Error: this operator cannot continue this calculation

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
In this case, the reason is that the seequence may contain only one `!=` operator;
another reaons causing this message would be a combination of `<` and `>` operators.

## Error: a calculation cannot end with an operator

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

This error message is complaining that it sees an operating ending the sequence.
This may be because there is no following expression or that the parser 
does not recognize the material after the last operator as the ending expression.

## Error: a forall statement with an ensures clause must have a body

```dafny
x
```
TODO

## XError: An initializing element display is allowed only for 1-dimensional arrays

```dafny
method m() {
  var a := new int[] [[1,2, 3,4]]
}
```
TODO

## Error: Expected 'to' or 'downto'

```dafny
method m(n: nat) {
  for i := n DownTo 0 {}
}
```

A for loop can express a computation to be performed for each value of a _loop index_.
In Dafny, the loop index is an int-based variable that is either 
- incremented up from a starting value to just before an ending value: `3 to 7` means 3, 4, 5, and 6
- or decremented from just below a starting value down to an ending value `7 downto 3` means 6, 5, 4, and 3.

The contextual keywords `to` and `downto` indicate incrementing and decrementing, respectively.
No other words are allowed here, including writing them with different case.

These two words have special meaning only in this part of a for-loop; they are not reserved words elsewhere.
That is, the code
```
method m() {
  var to: int := 6;
  var downto: int := 8;
  for to := to to downto {}
}
```
is legal, but is hardly recommended.

## Error: Ambiguous use of ==> and <==. Use parentheses to disambiguate.

```dafny
const b := true ==> false <== true;
```

The `==>` and `<==` operators have the same precedence but do not associate with each other.
You must use parentheses to show how they are grouped. Write the above example as either
`(true ==> false) <== true` or `true ==> (false <== true)`.

By contract `p ==> q ==> r` is `p ==> (q ==> r)` and
`p <== q <== r` is `(p <== q) <== r`.

See [this section](../DafnyRef/DafnyRef#sec-implication-and-reverse-implication) for more information.

TODO -- 2 instances

## Error: Ambiguous use of && and ||. Use parentheses to disambiguate.

```dafny
const b := true && false || true
```

The `&&` and `||` operators have the same precedence but do not associate with each other.
You must use parentheses to show how they are grouped. Write the above example as either
`(true && false) || true` or `true && (false || true)`.

TODOa -- 4 instances

## Error: chaining not allowed from the previous operator

```dafny
x
```
TODO

## Error: a chain cannot have more than one != operator

```dafny
const c := 1 != 2 != 3
```

[Chained operations](../DafnyRef/DafnyRef#sec-basic-types)
are a sequence of binary operations without parentheses: _a op b op c op d op e_.
But there are limitation on which operators can be in one chain together.

In particular for this error message, one cannot have chains that include more than one `!=` operator.

## Error: this operator chain cannot continue with an ascending operator

```dafny
const c := 4 > 3 < 2
```

[Chained operations](../DafnyRef/DafnyRef#sec-basic-types)
are a sequence of binary operations without parentheses: _a op b op c op d op e_.
But there are limitation on which operators can be in one chain together.

In particular for this error message, one cannot have chains that include both
less-than operations (either `<` or `<=`) and greter-than operations (either `>` or `>=`).


## Error: this operator chain cannot continue with a descending operator

```dafny
const c := 2 < 3 > 4
```

[Chained operations](../DafnyRef/DafnyRef#sec-basic-types)
are a sequence of binary operations without parentheses: _a op b op c op d op e_.
But there are limitation on which operators can be in one chain together.

In particular for this error message, one cannot have chains that include both
less-than operations (either `<` or `<=`) and greter-than operations (either `>` or `>=`).

## Error: can only chain disjoint (!!) with itself

```dafny
const c := 2 < 3 !! 4
```

[Chained operations](../DafnyRef/DafnyRef#sec-basic-types)
are a sequence of binary operations without parentheses: _a op b op c op d op e_.
But there are limitation on which operators can be in one chain together.
In particular for this error message, a disjoint operator (`!!`) can appear in a chain
only if all the operators in the chain are disjoint operators.

As described [here](../DafnyRef/DafnyRef#sec-collection-types),
`a !! b !! c !! d` means that `a`, `b`, `c`, and `d` are all mutually disjoint
(which is a slightly different rewriting of the chain than for other operations).

## Error: this operator cannot be part of a chain

```dafny
x
```
TODO

## Error: invalid RelOp

```dafny
x
```
TODO - IMPROVE

## Error: invalid RelOp (perhaps you intended \"!!\" with no intervening whitespace?)

```dafny
x
```

TODO - IMPROVE

## Error: Ambiguous use of &, |, ^. Use parentheses to disambiguate.

```dafny
const i: int := 5 | 6 & 7
```

The bit-operators `&`, `|`, and `^` have the same precedence but do not associate with each other.
So if they are used within the same expression, parentheses have to be used to show how they
are grouped. The abvoe example should be written as either `(5 | 6) & 7` or `5 | (6 & 7)`.

TODO - IMPROVE -- 3 instances

## Error: A forming expression must be a multiset

```dafny
x
```

 TODO

## Error: too many characters in character literal

```dafny
x
```

TODO: If this can happen at all it is with an unusual unicode char

A character literal consists of two `'` characters enclosing either
- a single ASCII character (that is not a backslash)
- a backslash-escaped character
- a sequence of characters designating a unicode character

More detail is given [here](../DafnyRef/DafnyRef#sec-character-constant-token) and [here](../DafnyRef/DafnyRef#sec-escaped-characters).;

## Error: binding not allowed in parenthesized expression

```dafny
method m() {
  var c := ( 4 := 5 );
}
```

A binding of the form `x := y` is used in map-display expresions, in which case they are enclosed in square brackets,
not parentheses. The above example should be `var c := [ 4 := 5 ]`

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

Within a function, the `:-` operator is limited to a most one left-hand-side and one-right-hand-side.

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

```dafny
x
```

TODO _ IMPROVE






