# 2. Lexical and Low Level Grammar {#sec-lexical-grammar}

As with most languages, Dafny syntax is defined in two levels. First the stream
of input characters is broken up into _tokens_. Then these tokens are parsed
using the Dafny grammar. 

The Dafny grammar is designed as an _attributed grammar_, which is a 
conventional BNF-style set of productions, but in which the productions can
have arguments. The arguments control some alternatives within
the productions, such as whether an alternative is allowed or not in a specific context.
These arguments allow for a more compact and understandable grammar.

The precise, technical details of the grammar are presented together in [Section 29](#sec-grammar-details).
The expository parts of this manual present the language structure less formally.
Throughout this document there are embedded hyperlinks to relevant grammar sections, 
marked as [grammar](#sec-grammar-details).

## 2.1. Dafny Input {#sec-unicode}

Dafny source code files are readable text encoded in UTF-8.
All program text other than the contents of comments, character, string and verbatim string literals
consists of printable and white-space ASCII characters,
that is, ASCII characters in the range `!` to `~`, plus space, tab, 
carriage return and newline (ASCII 9, 10, 13, 32) characters.

String and character literals and comments may contain any unicode character,
either directly or as an escape sequence.

## 2.2. Tokens and whitespace {#sec-token-types}
The characters used in a Dafny program fall into four groups:

* White space characters: space, tab, carriage return and newline
* alphanumerics: letters, digits, underscore (`_`), apostrophe (`'`), and question mark (`?`)
* punctuation: ``(){}[],.`;``
* operator characters (the other printable characters)

Except for string and character literals, each Dafny token consists of a 
sequence of consecutive characters from just one of these
groups, excluding white-space. White-space is ignored except that it
separates tokens and except in the bodies of character and string literals.

A sequence of alphanumeric characters (with no preceding or following additional
alphanumeric characters) is a _single_ token. This is true even if the token
is syntactically or semantically invalid and the sequence could be separated into
more than one valid token. For example, `assert56` is one identifier token,
not a keyword `assert` followed by a number; `ifb!=0` begins with the token
`ifb` and not with the keyword `if` and token `b`; `0xFFFFZZ` is an illegal
token, not a valid hex number `0xFFFF` followed by an identifier `ZZ`.
White-space must be used to separate two such tokens in a program.

Somewhat differently, operator tokens need not be separated.
Only specific sequences of operator characters are recognized and these
are somewhat context-sensitive. For example, in `seq<set<int>>`, the grammar
knows that `>>` is two individual `>` tokens terminating the nested
type parameter lists; the right shift operator `>>` would never be valid here. Similarly, the
sequence `==>` is always one token; even if it were invalid in its context,
separating it into `==` and `>` would always still be invalid.

In summary, except for required white space between alphanumeric tokens,
adding or removing white space between tokens can never result in changing the meaning of a Dafny program.
For most of this document, we consider Dafny programs as sequences of tokens.

## 2.3. Character Classes {#sec-character-classes}

This section defines character classes used later in the token definitions.
In this section 

* a backslash is used to start an escape sequence (so for example
`'\n'` denotes the single linefeed character)
* double quotes
enclose the set of characters constituting a character class
* enclosing single
quotes are used when there is just one character in the class
(perhaps expressed with a `\` escape character)
* `+` indicates
the union of two character classes
* `-` is the set-difference between the
two classes
* `ANY` designates all [unicode characters](#sec-unicode).

 name              | description
-------------------|---------------------------
letter             | ASCII upper or lower case letter; no unicode characters
digit              | base-ten digit ("0123456789")
posDigit           | digits, excluding 0 ("123456789")
posDigitFrom2      | digits excluding 0 and 1 ("23456789")
hexdigit           | a normal hex digit ("0123456789abcdefABCDEF")
special            | `?_"
cr                 | carriage return character (ASCII 10)
lf                 | line feed character (ASCII 13)
tab                | tab character (ASCII 9)
space              | space character (ASCII 32)
                   |
nondigitIdChar     | characters allowed in an identifier, except digits (letter + special)
idchar             | characters allowed in an identifier (nondigitIdChar + digits)
nonidchar          | characters not in identifiers (ANY - idchar)
charChar           | characters allowed in a character constant (ANY - '\'' - '\\' - cr - lf)
stringChar         | characters allowed in a string constant (ANY - '"' - '\\' - cr - lf)
verbatimStringChar | characters allowed in a verbatim string constant (ANY - '"')




The _special_ characters are the characters in addition to alphanumeric characters
that are allowed to appear in a Dafny identifier. These are

* `'` because mathematicians like to put primes on identifiers and some ML
  programmers like to start names of type parameters with a `'`,
* `_` because computer scientists expect to be able to have underscores in identifiers, and
* `?` because it is useful to have `?` at the end of names of predicates,
  e.g., `Cons?`.

A `nonidchar` is any character except those that can be used in an identifier.
Here the scanner generator will interpret `ANY` as any unicode character.
However, `nonidchar` is used only to mark the end of the `!in` token;
in this context any character other than [whitespace or printable ASCII](#sec-unicode)
will trigger a subsequent scanning or parsing error.



## 2.4. Comments {#sec-comments}
Comments are in two forms.

* They may go from `/*` to `*/` .
* They may go from `//` to the end of the line.

A comment is identified as a token during the tokenization of 
input text and is then discarded for the purpose of interpreting the 
Dafny program. (It is retained to enable auto-formatting
and provide accurate source locations for error messages.)
Thus comments are token separators: `a/*x*/b` becomes two tokens
`a` and `b`.

Comments may be nested,
but note that the nesting of multi-line comments is behavior that is different
from most programming languages. In Dafny,
<!-- %check-resolve -->
```dafny
method m() {
  /* comment
     /* nested comment
     */
     rest of outer comment
  */
}
```
is permitted; this feature is convenient for commenting out blocks of
program statements that already have multi-line comments within them.
Other than looking for end-of-comment delimiters,
the contents of a comment are not interpreted.
Comments may contain any characters.

Note that the nesting is not fool-proof. In
<!-- %check-resolve Grammar.1.expect -->
```dafny
method m() {
  /* var i: int;
     // */ line comment
     var j: int;
  */
}
```
and
<!-- %check-resolve Grammar.2.expect -->
```dafny
method m() {
  /* var i: int;
     var s: string := "a*/b";
     var j: int;
   */
}
```
the `*/` inside the line comment and the string are seen as the end of the outer
comment, leaving trailing text that will provoke parsing errors.

## 2.5. Tokens ([grammar](#sec-g-tokens)) {#sec-tokens}

The Dafny tokens are defined in this section.

### 2.5.1. Reserved Words {#sec-reserved-words}

Dafny has a set of reserved words that may not
be used as identifiers of user-defined entities.
These are listed [here](#sec-g-tokens).

In particular note that

- `array`, `array2`, `array3`, etc. are reserved words, denoting array types of given rank.
However,  `array1` and `array0` are ordinary identifiers.
- `array?`, `array2?`, `array3?`, etc. are reserved words, 
denoting possibly-null array types of given rank,
but not `array1?` or `array0?`.
- `bv0`, `bv1`, `bv2`, etc. are reserved words that denote the types of
bitvectors of given length.
The sequence of digits after 'array' or 'bv' may not have leading zeros: 
for example, `bv02` is an ordinary identifier.

### 2.5.2. Identifiers {#sec-identifiers}

In general, an `ident` token (an identifier) is a sequence of ``idchar`` characters where
the first character is a ``nondigitIdChar``. However tokens that fit this pattern
are not identifiers if they look like a character literal
or a reserved word (including array or bit-vector type tokens).
Also, `ident` tokens that begin with an `_` are not permitted as user identifiers.

### 2.5.3. Digits {#sec-digits}

A `digits` token is a sequence of decimal digits (`digit`), possibly interspersed with underscores for readability (but not beginning or ending with an underscore).
Example: `1_234_567`.

A `hexdigits` token denotes a hexadecimal constant, and is a sequence of hexadecimal digits (`hexdigit`)
prefaced by `0x` and
 possibly interspersed with underscores for readability (but not beginning or ending with an underscore).
Example: `0xffff_ffff`.

A `decimaldigits` token is a decimal fraction constant, possibly interspersed with underscores for readability (but not beginning or ending with an underscore).
It has digits both before and after a single period (`.`) character. There is no syntax for floating point numbers with exponents.
Example: `123_456.789_123`.

### 2.5.4. Escaped Character {#sec-escaped-characters}

The `escapedChar` token is a multi-character sequence that denotes a non-printable or non-ASCII character.
They begin with a backslash characcter (`\`) and denote
 a single- or double-quote character, backslash,
null, new line, carriage return, tab, or a
Unicode character with given hexadecimal representation.
Which Unicode escape form is allowed depends on the value of the `--unicode-char` option.

If `--unicode-char:false` is stipulated,
`\uXXXX` escapes can be used to specify any UTF-16 code unit.

If `--unicode-char:true` is stipulated,
`\U{X..X}` escapes can be used to specify any Unicode scalar value.
There must be at least one hex digit in between the braces, and at most six.
Surrogate code points are not allowed.
The hex digits may be interspersed with underscores for readability 
(but not beginning or ending with an underscore), as in `\U{1_F680}`.
The braces are part of the required character sequence.


### 2.5.5. Character Constant Token {#sec-character-constant-token}

The `charToken` token denotes a character constant.
It is either a `charChar` or an `escapedChar` enclosed in single quotes.
Note that although Unicode
letters are not allowed in Dafny identifiers, Dafny does support [Unicode
in its character, string, and verbatim strings constants and in its comments](#sec-unicode).


### 2.5.6. String Constant Token {#sec-string-constant-token}

A `stringToken` denotes a string constant.
It consists of a sequence of `stringChar` and `escapedChar` characters enclosed in 
double quotes.

A `verbatimStringToken` token also denotes a string constant.
It is a sequence of any `verbatimStringChar` characters (which includes newline characters),
enclosed between `@"` and `"`, except that two
successive double quotes represent one quote character inside
the string. This is the mechanism for escaping a double quote character,
which is the only character needing escaping in a verbatim string.
Within a verbatim string constant, a backslash character represents itself 
and is not the first character of an `escapedChar`.

### 2.5.7. Ellipsis {#sec-ellipsis}

The `ellipsisToken` is the character sequence `...` and is typically used to designate something missing that will
later be inserted through refinement or is already present in a parent declaration.

## 2.6. Low Level Grammar Productions {#sec-grammar}

### 2.6.1. Identifier Variations {#sec-identifier-variations}

#### 2.6.1.1. Identifier

A basic ordinary identifier is just an `ident` token.

It may be followed by a sequence of suffixes to denote compound entities.
Each suffix is a dot (`.`) and another token, which may be

- another `ident` token
- a `digits` token
- the `requires` reserved word
- the `reads` reserved word

Note that

* Digits can be used to name fields of classes and destructors of
  datatypes. For example, the built-in tuple datatypes have destructors
  named 0, 1, 2, etc. Note that as a field or destructor name a digit sequence
  is treated as a string, not a number: internal
  underscores matter, so `10` is different from `1_0` and from `010`.
* `m.requires` is used to denote the [precondition](#sec-requires-clause) for method `m`.
* `m.reads` is used to denote the things that method `m` may [read](#sec-reads-clause).

#### 2.6.1.2. No-underscore-identifier

A `NoUSIdent` is an identifier except that identifiers with a **leading**
underscore are not allowed. The names of user-defined entities are
required to be ``NoUSIdent``s or, in some contexts, a ``digits``.
 We introduce more mnemonic names
for these below (e.g. ``ClassName``).

A no-underscore-identifier is required for the following:

- module name
- class or trait name
- datatype name
- newtype name
- synonym (and subset) type name
- iterator name
- type variable name
- attribute name

A variation, a no-underscore-identifier or a `digits`, is allowed for

- datatype member name
- method or function or constructor name
- label name
- export id
- suffix that is a typename or constructor 

All _user-declared_ names do not start with underscores, but there are
internally generated names that a user program might _use_ that begin
with an underscore or are just an underscore.

#### 2.6.1.3. Wild identifier {#sec-wild-identifier}

A wild identifier is a no-underscore-identifier except that the singleton
`_` is allowed. The `_` is replaced conceptually by a unique
identifier distinct from all other identifiers in the program.
A `_` is used when an identifier is needed, but its content is discarded.
Such identifiers are not used in expressions.

Wild identifiers may be used in these contexts:

- formal parameters of a lambda expression
- the local formal parameter of a quantifier
- the local formal parameter of a subset type or newtype declaration
- a variable declaration
- a case pattern formal parameter
- binding guard parameter
- for loop parameter
- LHS of update statements 

### 2.6.2. Qualified Names

A qualified name starts with the name of a top-level entity and then is followed by
zero or more ``DotSuffix``s which denote a component. Examples:

* `Module.MyType1`
* `MyTuple.1`
* `MyMethod.requires`
* `A.B.C.D`

### 2.6.3. Identifier-Type Combinations

Identifiers are typically declared in combination with a type, as in
<!-- %no-check -->
```dafny
var i: int
```

However, Dafny infers types in many circumstances, and in those, the type can be omitted. The type is required
for field declarations and formal parameters of methods, functions and constructors (because there is no initializer).
It may be omitted (if the type can be inferred) for local variable declarations, pattern matching variables, 
quantifiers, 

Similarly, there are circumstances in which the identifier name is not needed, because it is not used.
This is allowed in defining algebraic datatypes.

In some other situations a wild identifier can be used, as described [above](#sec-wild-identifier).

### 2.6.4. Quantifier Domains ([grammar](#g-quantifier-domain)) {#sec-quantifier-domains}

Several Dafny constructs bind one or more variables to a range of possible values.
For example, the quantifier `forall x: nat | x <= 5 :: x * x <= 25` has the meaning
"for all integers x between 0 and 5 inclusive, the square of x is at most 25".
Similarly, the set comprehension `set x: nat | x <= 5 :: f(x)` can be read as
"the set containing the result of applying f to x, for each integer x from 0 to 5 inclusive".
The common syntax that specifies the bound variables and what values they take on
is known as the *quantifier domain*; in the previous examples this is `x: nat | x <= 5`, 
which binds the variable `x` to the values `0`, `1`, `2`, `3`, `4`, and `5`.

Here are some more examples.

- `x: byte` (where a value of type `byte` is an int-based number `x` in the range `0 <= x < 256`)
- `x: nat | x <= 5`
- `x <- integerSet`
- `x: nat <- integerSet`
- `x: nat <- integerSet | x % 2 == 0`
- `x: nat, y: nat | x < 2 && y < 2`
- `x: nat | x < 2, y: nat | y < x`
- `i | 0 <= i < |s|, y <- s[i] | i < y`

A quantifier domain declares one or more *quantified variables*, separated by commas.
Each variable declaration can be nothing more than a variable name, but it 
may also include any of three optional elements:

1. The optional syntax `: T` declares the type of the quantified variable.
   If not provided, it will be inferred from context.

2. The optional syntax `<- C` attaches a collection expression `C` as a *quantified variable domain*.
   Here a collection is any value of a type that supports the `in` operator, namely sets, multisets, maps, and sequences.
   The domain restricts the bindings to the elements of the collection: `x <- C` implies `x in C`.
   The example above can also be expressed as `var c := [0, 1, 2, 3, 4, 5]; forall x <- c :: x * x <= 25`.

3. The optional syntax `| E` attaches a boolean expression `E` as a *quantified variable range*,
   which restricts the bindings to values that satisfy this expression.
   In the example above `x <= 5` is the range attached to the `x` variable declaration.

Note that a variable's domain expression may reference any variable declared before it,
and a variable's range expression may reference the attached variable (and usually does) and any variable declared before it.
For example, in the quantifier domain `i | 0 <= i < |s|, y <- s[i] | i < y`, the expression `s[i]` is well-formed
because the range attached to `i` ensures `i` is a valid index in the sequence `s`.

Allowing per-variable ranges is not fully backwards compatible, and so it is not yet allowed by default;
the `/quantifierSyntax:4` option needs to be provided to enable this feature (See [Section 25.8.5](#sec-controlling-language)).

### 2.6.5. Numeric Literals ([grammar](#g-literal-expression)) {#sec-numeric-literals}

Integer and bitvector literals may be expressed in either decimal or hexadecimal (`digits` or `hexdigits`).

Real number literals are written as decimal fractions (`decimaldigits`).

