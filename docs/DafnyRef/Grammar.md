# 2. Lexical and Low Level Grammar {#sec-lexical-grammar}

The Dafny grammar is designed as an _attributed grammar_, which is a 
conventional BNF-style set of productions, but in which the productions can
have arguments. The arguments control some alternatives within
the productions, such as whether an alternative is allowed or not in a specific context.
These arguments allow for a more compact and understandable grammar.

The precise, technical details of the grammar are combined in [Section 29](#sec-grammar-details).
The expository parts of this manual present the language structure less formally.

## 2.1. Dafny Input {#sec-unicode}

Dafny source code files are readable text encoded in UTF-8.
All program text other than the contents of comments, character, string and verbatim string literals
consists of printable and white-space ASCII characters,
that is, ASCII characters in the range `!` to `~`, plus space, tab, 
carriage return and newline (ASCII, 9, 10, 13, 32) characters.

## 2.2. Tokens and whitespace {#sec-token-types}
The characters used in a Dafny program fall into four groups:

* White space characters
* alphanumerics: letters, digits, underscore (`_`), apostrophe (`'`), and question mark (`?`)
* punctuation: ``(){}[],.`;``
* operator characters (the other printable characters)

Each Dafny token consists of a sequence of consecutive characters from just one of these
groups, excluding white-space. White-space is ignored except that it
separates tokens, except in the bodies of character and string literals.

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
adding white space between tokens or removing white space can never result in changing the meaning of a Dafny program.
For the rest of this document, we consider Dafny programs as sequences of tokens.

## 2.3. Character Classes {#sec-character-classes}
This section defines character classes used later in the token definitions.
In this section a backslash is used to start an escape sequence; so for example
`'\n'` denotes the single linefeed character. Also in this section, double quotes
enclose the set of characters constituting a character class; enclosing single
quotes are used when there is just one character in the class. `+` indicates
the union of two character classes; `-` is the set-difference between the
two classes. `ANY` designates all [unicode characters](#sec-unicode).

 name | description
----------------------------|---------------------------
letter | ASCII upper or lower case letter (a-zA-Z); no unicode characters
digit | base-ten digit (0-9)
posDigit | digits, excluding 0 (1-9)
posDigitFrom2 | digits excluding 0 and 1 (2-9)
hexdigit | normal hex digits (0-9a-fA-F)
special | ' ? or _
cr      | carriage return character ('\r')
lf      | line feed character ('\n')
tab     | tab character ('\t')
space   | space character (' ')


````grammar
letter = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
````
At present, a letter is an ASCII upper or lowercase letter. Other Unicode letters
are not supported.

````grammar
digit = "0123456789"
````
A digit is just one of the base-10 digits.

````grammar
posDigit = "123456789"
posDigitFrom2 = "23456789"
````
A ``posDigit`` is a digit, excluding 0. ``posDigitFrom2`` excludes both 0 and 1.

````grammar
hexdigit = "0123456789ABCDEFabcdef"
````
A ``hexdigit`` character is a digit or one of the letters from 'A' to 'F' in either case.

````grammar
special = "'_?"
````
The _special_ characters are the characters in addition to alphanumeric characters
that are allowed to appear in a Dafny identifier. These are

* `'` because mathematicians like to put primes on identifiers and some ML
  programmers like to start names of type parameters with a `'`,
* `_` because computer scientists expect to be able to have underscores in identifiers, and
* `?` because it is useful to have `?` at the end of names of predicates,
  e.g., "Cons?".

````grammar
cr        = '\r'
````
A carriage return character.

````grammar
lf        = '\n'
````
A line feed character.

````grammar
tab       = '\t'
````
A tab character.

````grammar
space     = ' '
````
A space character.

````grammar
nondigitIdChar = letter + special
````
The characters that can be used in an identifier minus the digits.

````grammar
idchar = nondigitIdChar + digit
````
The characters that can be used in an identifier.

````grammar
nonidchar = ANY - idchar
````
Any character except those that can be used in an identifier.
Here the scanner generator will interpret `ANY` as any unicode character.
However, `nonidchar` is used only to mark the end of the `!in` token;
in this context any character other than [whitespace or printable ASCII](#sec-unicode)
will trigger a subsequent scanning or parsing error.

````grammar
charChar = ANY - '\'' - '\\' - cr - lf
````
Characters that can appear in a character constant.

````grammar
stringChar = ANY - '"' - '\\' - cr - lf
````
Characters that can appear in a string constant.

````grammar
verbatimStringChar = ANY - '"'
````
Characters that can appear in a verbatim string.

## 2.4. Comments {#sec-comments}
Comments are in two forms.

* They may go from `/*` to `*/` .
* They may go from `//` to the end of the line.

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

## 2.5. Tokens {#sec-tokens}
As with most languages, Dafny syntax is defined in two levels. First the stream
of input characters is broken up into _tokens_. Then these tokens are parsed
using the Dafny grammar. The Dafny tokens are defined in this section.

### 2.5.1. Reserved Words {#sec-reserved-words}
The following reserved words appear in the Dafny grammar and may not be used
as identifiers of user-defined entities:

````grammar
reservedword =
    "abstract" | "allocated" | "as" | "assert" | "assume" |
    "bool" | "break" | "by" |
    "calc" | "case" | "char" | "class" | "codatatype" |
    "const" | "constructor" |
    "datatype" | "decreases" |
    "else" | "ensures" | "exists" | "export" | "extends" |
    "false" | "forall" | "fresh" | "function" | "ghost" |
    "if" | "imap" | "import" | "in" | "include" |
    "int" | "invariant" | "is" | "iset" | "iterator" |
    "label" | "lemma" | "map" | "match" | "method" |
    "modifies" | "modify" | "module" | "multiset" |
    "nameonly" | "nat" | "new" | "newtype" | "null" |
    "object" | "object?" | "old" | "opened" | "ORDINAL"
    "predicate" | "print" | "provides" |
    "reads" | "real" | "refines" | "requires" | "return" |
    "returns" | "reveal" | "reveals" |
    "seq" | "set" | "static" | "string" |
    "then" | "this" | "trait" | "true" | "twostate" | "type" |
    "unchanged" | "var" | "while" | "witness" |
    "yield" | "yields" |
    arrayToken | bvToken

arrayToken = "array" [ posDigitFrom2 | posDigit digit { digit }]["?"]

bvToken = "bv" ( 0 | posDigit { digit } )
````

An ``arrayToken`` is a reserved word that denotes an array type of
given rank. `array` is an array type of rank 1 (aka a vector). `array2`
is the type of two-dimensional arrays, etc.
`array1` and `array1?` are not reserved words; they are just ordinary identifiers.
Similarly, `bv0`, `bv1`, and `bv8` are reserved words, but `bv02` is an
ordinary identifier.

### 2.5.2. Identifiers {#sec-identifiers}

````grammar
ident = nondigitIdChar { idchar } - charToken - reservedword
````
In general Dafny identifiers are sequences of ``idchar`` characters where
the first character is a ``nondigitIdChar``. However tokens that fit this pattern
are not identifiers if they look like a character literal
or a reserved word (including array or bit-vector type tokens).
Also, `ident` tokens that begin with an `_` are not permitted as user identifiers.

### 2.5.3. Digits {#sec-digits}
````grammar
digits = digit {['_'] digit}
````

A sequence of decimal digits, possibly interspersed with underscores for readability (but not beginning or ending with an underscore).
Example: `1_234_567`.
````grammar
hexdigits = "0x" hexdigit {['_'] hexdigit}
````

A hexadecimal constant, possibly interspersed with underscores for readability (but not beginning or ending with an underscore).
Example: `0xffff_ffff`.

````grammar
decimaldigits = digit {['_'] digit} '.' digit {['_'] digit}
````
A decimal fraction constant, possibly interspersed with underscores for readability (but not beginning or ending with an underscore).
Example: `123_456.789_123`.

### 2.5.4. Escaped Character {#sec-escaped-characters}
In this section the "\\" characters are literal.
````grammar
escapedChar =
    ( "\'" | "\"" | "\\" | "\0" | "\n" | "\r" | "\t"
      | "\u" hexdigit hexdigit hexdigit hexdigit
      | "\U{" hexdigit { hexdigit } "}"
    )
````

In Dafny character or string literals, escaped characters may be used
to specify the presence of a single- or double-quote character, backslash,
null, new line, carriage return, tab, or a
Unicode character with given hexadecimal representation.
Which Unicode escape form is allowed depends on the value of the `--unicode-char` option.

If `--unicode-char:false` is provided,
`\uXXXX` escapes can be used to specify any UTF-16 code unit.

If `--unicode-char:true` is provided,
`\U{X..X}` escapes can be used to specify any Unicode scalar value.
There must be at least one hex digit in between the braces, and at most six.
Surrogate code points are not allowed.
The hex digits may be interspersed with underscores for readability 
(but not beginning or ending with an underscore), as in `\U{1_F680}`.


### 2.5.5. Character Constant Token {#sec-character-constant-token}
````grammar
charToken = "'" ( charChar | escapedChar ) "'"
````

A character constant is enclosed by `'` and includes either a character
from the ``charChar`` set or an escaped character. Note that although Unicode
letters are not allowed in Dafny identifiers, Dafny does support [Unicode
in its character, string, and verbatim strings constants and in its comments](#sec-unicode). A character
constant has type `char`.


### 2.5.6. String Constant Token {#sec-string-constant-token}
````grammar
stringToken =
    '"' { stringChar | escapedChar }  '"'
  | '@' '"' { verbatimStringChar | '"' '"' } '"'
````

A string constant is either a normal string constant or a verbatim string constant.
A normal string constant is enclosed by `"` and can contain characters from the
``stringChar`` set and ``escapedChar``s.

A verbatim string constant is enclosed between `@"` and `"` and can
consist of any characters (including newline characters) except that two
successive double quotes represent one quote character inside
the string. This is the mechanism for escaping a double quote character,
which is the only character needing escaping in a verbatim string.
Within a verbatim string constant, a backslash character represents itself and is not the first character of an `escapedChar`.

### 2.5.7. Ellipsis {#sec-ellipsis}
````grammar
ellipsis = "..."
````
The ellipsis symbol is typically used to designate something missing that will
later be inserted through refinement or is already present in a parent declaration.

## 2.6. Low Level Grammar Productions {#sec-grammar}

### 2.6.1. Identifier Variations {#sec-identifier-variations}

````grammar
Ident = ident
````
The ``Ident`` non-terminal is just an ``ident`` token and represents an ordinary
identifier.

````grammar
DotSuffix =
  ( ident | digits | "requires" | "reads" )
````
When using the _dot_ notation to denote a component of a compound entity,
the token following the "." may be an identifier,
 a natural number, or one of the keywords `requires` or `reads`.

* Digits can be used to name fields of classes and destructors of
  datatypes. For example, the built-in tuple datatypes have destructors
  named 0, 1, 2, etc. Note that as a field or destructor name a digit sequence
  is treated as a string, not a number: internal
  underscores matter, so `10` is different from `1_0` and from `010`.
* `m.requires` is used to denote the [precondition](#sec-requires-clause) for method `m`.
* `m.reads` is used to denote the things that method `m` may [read](#sec-reads-clause).

````grammar
NoUSIdent = ident - "_" { idchar }
````
A ``NoUSIdent`` is an identifier except that identifiers with a **leading**
underscore are not allowed. The names of user-defined entities are
required to be ``NoUSIdent``s or, in some contexts, a ``digits``.
 We introduce more mnemonic names
for these below (e.g. ``ClassName``).

````grammar
WildIdent = NoUSIdent | "_"
````
Identifier, disallowing leading underscores, except the "wildcard"
identifier `_`. When `_` appears it is replaced by a unique generated
identifier distinct from user identifiers. This wildcard has several uses
in the language, but it is not used as part of expressions.

### 2.6.2. NoUSIdent Synonyms
In the productions for the declaration of user-defined entities the name of the
user-defined entity is required to be an identifier that does not start
with an underscore, i.e., a ``NoUSIdent``. To make the productions more
mnemonic, we introduce the following synonyms for ``NoUSIdent``
and other identifier-related symbols.

````grammar
IdentOrDigits = Ident | digits
NoUSIdentOrDigits = NoUSIdent | digits
ModuleName = NoUSIdent
ClassName = NoUSIdent    // also traits
DatatypeName = NoUSIdent
DatatypeMemberName = NoUSIdentOrDigits
NewtypeName = NoUSIdent
SynonymTypeName = NoUSIdent
IteratorName = NoUSIdent
TypeVariableName = NoUSIdent
MethodFunctionName = NoUSIdentOrDigits
LabelName = NoUSIdentOrDigits
AttributeName = NoUSIdent
ExportId = NoUSIdentOrDigits
TypeNameOrCtorSuffix = NoUSIdentOrDigits
````


### 2.6.3. Qualified Names
```grammar
ModuleQualifiedName = ModuleName { "." ModuleName }
```
A qualified name starts with the name of the top-level entity and then is followed by
zero or more ``DotSuffix``s which denote a component. Examples:

* `Module.MyType1`
* `MyTuple.1`
* `MyMethod.requires`
* `A.B.C.D`

The grammar does not actually have a production for qualified names
except in the special case of a qualified name that is known to be
a module name, i.e. a ``ModuleQualifiedName``.

### 2.6.4. Identifier-Type Combinations
In this section, we describe some nonterminals that combine an identifier and a type.

````grammar
IdentType = WildIdent ":" Type
````
In Dafny, a variable or field is typically declared by giving its name followed by
a ``colon`` and its type. An ``IdentType`` is such a construct.

````grammar
FIdentType = NoUSIdentOrDigits ":" Type
````
A `FIdentType` is used to declare a field. The Type is required because there is no initializer.

````grammar
CIdentType = NoUSIdentOrDigits [ ":" Type ]
````
A `CIdentType` is used for a `const` declaration. The Type is optional because it may be inferred from
the initializer.

````grammar
GIdentType(allowGhostKeyword, allowNewKeyword, allowOlderKeyword, allowNameOnlyKeyword, allowDefault) =
    { "ghost" | "new" | "nameonly" | "older" } IdentType
    [ ":=" Expression(allowLemma: true, allowLambda: true) ]
````
A ``GIdentType`` is a typed entity declaration optionally preceded by `ghost` or `new`. The _ghost_
qualifier means the entity is only used during verification and not in the generated code.
Ghost variables are useful for abstractly representing internal state in specifications.
If `allowGhostKeyword` is false, then `ghost` is not allowed.
If `allowNewKeyword` is false, then `new` is not allowed.
If `allowNameOnlyKeyword` is false, then `nameonly` is not allowed.
If `allowDefault` is false, then `:= Expression` is not allowed.

`older` is a context-sensitive keyword. It is recognized as a keyword only by `GIdentType` and
only when `allowOlderKeyword` is true. If `allowOlderKeyword` is false, then a use of `older`
is parsed by the `IdentType` production in `GIdentType`.


````grammar
LocalIdentTypeOptional = WildIdent [ ":" Type ]
````
A ``LocalIdentTypeOptional`` is used when declaring local variables.
If a value is specified for the variable, the
type may be omitted because it can be inferred from the initial value.
An initial value is not required.

````grammar
IdentTypeOptional = WildIdent [ ":" Type ]
````
A ``IdentTypeOptional`` is typically used in a context where the type of the identifier
may be inferred from the context. Examples are in pattern matching or quantifiers.

````grammar
TypeIdentOptional =
    { "ghost" | "nameonly" } [ NoUSIdentOrDigits ":" ] Type
    [ ":=" Expression(allowLemma: true, allowLambda: true) ]
````
``TypeIdentOptional``s are used in ``FormalsOptionalIds``. This represents situations
where a type is given but there may not be an identifier. The default-value expression
`:= Expression` is allowed only if `NoUSIdentOrDigits :` is also provided.
If modifier `nameonly` is given, then `NoUSIdentOrDigits` must also be used.

````grammar
FormalsOptionalIds = "(" [ TypeIdentOptional
                           { "," TypeIdentOptional } ] ")"
````
A ``FormalsOptionalIds`` is a formal parameter list in which the types are required
but the names of the parameters are optional. This is used in algebraic
datatype definitions.

### 2.6.5. Quantifier Domains {#sec-quantifier-domains}

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

The general production for quantifier domains is:

````grammar
QuantifierDomain(allowLemma, allowLambda) =
    QuantifierVarDecl(allowLemma, allowLambda) 
    { "," QuantifierVarDecl(allowLemma, allowLambda) }

QuantifierVarDecl(allowLemma, allowLambda) =
    IdentTypeOptional
    [ <- Expression(allowLemma, allowLambda) ]
    { Attribute }
    [ | Expression(allowLemma, allowLambda) ]
````

### 2.6.6. Numeric Literals {#sec-numeric-literals}
````grammar
Nat = ( digits | hexdigits )
````
A ``Nat`` represents a natural number expressed in either decimal or hexadecimal.

````grammar
Dec = decimaldigits
````
A ``Dec`` represents a decimal fraction literal.
