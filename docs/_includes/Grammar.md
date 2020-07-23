# Lexical and Low Level Grammar
Dafny uses the Coco/R lexer and parser generator for its lexer and parser
(<http://www.ssw.uni-linz.ac.at/Research/Projects/Coco>)[@Linz:Coco].
The Dafny input file to Coco/R is the `Dafny.atg` file in the source tree.
A Coco/R input file consists of code written in the target language
(e.g. C\#) intermixed with these special sections:

0. The [Characters section][#sec-character-classes]
    which defines classes of characters that are used
   in defining the lexer.
1. The [Tokens section][#sec-tokens] which defines the lexical tokens.
2. The [Productions section][#sec-grammar]
 which defines the grammar. The grammar productions
are distributed in the later parts of this document in the parts where
those constructs are explained.

The grammar presented in this document was derived from the `Dafny.atg`
file but has been simplified by removing details that, though needed by
the parser, are not needed to understand the grammar. In particular, the
following transformations have been performed.

* The semantics actions, enclosed by "(." and ".)", were removed.
* There are some elements in the grammar used for error recovery
  ("SYNC"). These were removed.
* There are some elements in the grammar for resolving conflicts
  ("IF(b)"). These have been removed.
* Some comments related to Coco/R parsing details have been removed.
* A Coco/R grammar is an attributed grammar where the attributes enable
  the productions to have input and output parameters. These attributes
  were removed except that boolean input parameters that affect
  the parsing are kept.
  * In our representation we represent these
    in a definition by giving the names of the parameters following
    the non-terminal name. For example `entity1(allowsX)`.
  * In the case of uses of the parameter, the common case is that the
    parameter is just passed to a lower-level non-terminal. In that
    case we just give the name, e.g. `entity2(allowsX)`.
  * If we want to given an explicit value to a parameter, we specify it in
    a keyword notation like this: `entity2(allowsX: true)`.
  * In some cases the value to be passed depends on the grammatical context.
    In such cases we give a description of the conditions under which the
    parameter is true, enclosed in parenthesis. For example:

      `FunctionSignatureOrEllipsis_(allowGhostKeyword: ("method" present))`

    means that the `allowGhostKeyword` parameter is true if the
    "method" keyword was given in the associated ``FunctionDecl``.
  * Where a parameter affects the parsing of a non-terminal we will
    explain the effect of the parameter.


The names of character sets and tokens start with a lower case
letter but the names of grammar non-terminals start with
an upper-case letter.

The grammar uses Extended BNF notation. See the [Coco/R Referenced
manual](http://www.ssw.uni-linz.ac.at/Research/Projects/Coco/Doc/UserManual.pdf)
for details. But in summary:

* identifiers starting with a lower case letter denote
terminal symbols,
* identifiers starting with an upper case letter denote nonterminal
symbols.
* Strings (a sequence of characters enclosed by double quote characters)
denote the sequence of enclosed characters.
* `=` separates the sides of a production, e.g. `A = a b c`
* In the Coco grammars "." terminates a production, but for readability
  in this document a production starts with the defined identifier in
  the left margin and may be continued on subsequent lines if they
  are indented.
* `|` separates alternatives, e.g. `a b | c | d e` means `a b` or `c or d e`
* `(` `)` groups alternatives, e.g. `(a | b) c` means `a c` or `b c`
* `[ ]` option, e.g. `[a] b` means `a b` or `b`
* `{ }` iteration (0 or more times), e.g. `{a} b` means `b` or `a b` or `a a b` or ...
* We allow `|` inside `[ ]` and `{ }`. So `[a | b]` is short for `[(a | b)]`
  and `{a | b}` is short for `{(a | b)}`.
* The first production defines the name of the grammar, in this case `Dafny`.

In addition to the Coco rules, for the sake of readability we have adopted
these additional conventions.

* We allow `-` to be used. `a - b` means it matches if it matches `a` but not `b`.
* To aid in explaining the grammar we have added some additional productions
that are not present in the original grammar. We name these with a trailing
underscore. If you inline these where they are referenced, the result should
let you reconstruct the original grammar.

**For the convenience of the reader, any references to character sets,
tokens, or grammar non-terminals in this document are hyper-links that
will link to the definition of the entity.**

<!-- TODO: Those grammar hyperlinks are not implemented -->

## Character Classes {#sec-character-classes}
This section defines character classes used later in the token definitions.
In this section a backslash is used to start an escape sequence; so for example
`'\n'` denotes the single linefeed character. Also in this section, double quotes
enclose the set of characters constituting a character class; enclosing single
quotes are used when there is just one character in the class. `+` indicates
the union of two character classes; `-` is the set-difference between the 
two classes. `ANY` designates all ASCII characters.

````
letter = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
````
At present, a letter is an ASCII upper or lowercase letter. Other Unicode letters
are not supported.

````
digit = "0123456789"
````
A digit is just one of the base-10 digits.

````
posDigit = "123456789"
````
A ``posDigit`` is a digit, excluding 0.

````
hexdigit = "0123456789ABCDEFabcdef"
````
A ``hexdigit`` character is a digit or one of the letters from 'A' to 'F' in either case.

````
special = "'_?"
````
The _special_ characters are the characters in addition to alphanumeric characters
that are allowed to appear in a Dafny identifier. These are

* `'` because mathematicians like to put primes on identifiers and some ML
  programmers like to start names of type parameters with a "'".
* `_` because computer scientists expect to be able to have underscores in identifiers.
* `?` because it is useful to have "?" at the end of names of predicates,
  e.g. "Cons?".

````
cr        = '\r'
````
A carriage return character.

````
lf        = '\n'
````
A line feed character.

````
tab       = '\t'
````
A tab character.

````
space     = ' '
````
A space character.

````
nondigitIdChar = letter + special
````
The characters that can be used in an identifier minus the digits.

````
idchar = nondigitIdChar + digit
````
The characters that can be used in an identifier.

````
nonidchar = ANY - idchar
````
Any character except those that can be used in an identifier.

````
charChar = ANY - '\'' - '\\' - cr - lf
````
Characters that can appear in a character constant.

````
stringChar = ANY - '"' - '\\' - cr - lf
````
Characters that can appear in a string constant.

````
verbatimStringChar = ANY - '"'
````
Characters that can appear in a verbatim string.

### Comments
Comments are in two forms.

* They may go from "/\*" to "\*/" and be nested.
* They may go from "//" to the end of the line.

Note that the nesting of multi-line comments is behavior that is different 
from most programming languages. In dafny,
```
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

## Tokens {#sec-tokens}
As with most languages, Dafny syntax is defined in two levels. First the stream
of input characters is broken up into _tokens_. Then these tokens are parsed
using the Dafny grammar. The Dafny tokens are defined in this section.

### Reserved Words
The following reserved words appear in the Dafny grammar and may not be used
as identifiers of user-defined entities:

```
reservedword =
    "abstract" | "array" | "as" | "assert" | "assume" | "bool" | 
    "break" | "calc" | "case" | "char" | "class" | "codatatype" | 
    "colemma" | "constructor" | "copredicate" | "datatype" | "decreases" |
    "default" | "else" | "ensures" | "exists" | "extends" | "false" |
    "forall" | "free" | "fresh" | "function" | "ghost" | "if" | "imap" | "import" |
    "in" | "include" | "inductive" | "int" | "invariant" | "iset" | "iterator" | "label" |
    "lemma" | "map" | "match" | "method" | "modifies" | "modify" |
    "module" | "multiset" | "nat" | "new" | "newtype" | "null" | "object" |
    "old" | "opened" | "predicate" | "print" | "protected" |
    "reads" | "real" | "refines" | "requires" | "return" | "returns" | "seq" |
    "set" | "static" | "string" | "then" | "this" | "trait" | "true" | "type" |
    "var" | "where" | "while" | "yield" | "yields" | arrayToken

arrayToken = "array" [ posDigit { digit }]
```

An ``arrayToken`` is a reserved word that denotes an array type of
given rank. `array` is an array type of rank 1 (aka a vector). `array2`
is the type of two-dimensional arrays, etc.

TODO: Is "_" is reserved word?

### Identifiers

````
ident = nondigitIdChar { idchar } - arraytoken - chartoken - reservedword
````
In general Dafny identifiers are sequences of ``idChar`` characters where
the first character is a ``nondigitIdChar``. However tokens that fit this pattern
are not identifiers if they look like an array type token, a character literal,
or a reserved word.

### Digits
````
digits = digit {['_'] digit}
````

A sequence of decimal digits, possibly interspersed with underscores for readability. Example: `1_234_567`.
````
hexdigits = "0x" hexdigit {['_'] hexdigit}
````

A hexadecimal constant, possibly interspersed with underscores for readability.
Example: `0xffff_ffff`.

````
decimaldigits = digit {['_'] digit} '.' digit {['_'] digit}
````
A decimal fraction constant, possibly interspersed with underscores for readability.
Example: `123_456.789_123`.

### Escaped Character
In this section the "\\" characters are literal.
````
escapedChar =
    ( "\'" | "\"" | "\\" | "\0" | "\n" | "\r" | "\t"
      | "\u" hexdigit hexdigit hexdigit hexdigit
    )
````

In Dafny character or string literals, escaped characters may be used
to specify the presence of a single- or double-quote character, backslash,
null, new line, carriage return, tab, or a
Unicode character with given hexadecimal representation.

### Character Constant Token
````
charToken = "'" ( charChar | escapedChar ) "'"
````

A character constant is enclosed by "'" and includes either a character
from the ``charChar`` set, or an escaped character. Note that although Unicode
letters are not allowed in Dafny identifiers, Dafny does support Unicode
in its character and string constants and in its data. A character
constant has type `char`.


### String Constant Token
````
stringToken =
    '"' { stringChar | escapedChar }  '"'
  | '@' '"' { verbatimStringChar | '"' '"' } '"'
````

A string constant is either a normal string constant or a verbatim string constant.
A normal string constant is enclosed by `"` and can contain characters from the
``stringChar`` set and escapes.

A verbatim string constant is enclosed between `@"` and `"` and can
consist of any characters (including newline characters) except that two
successive double quotes represent one quote character inside
the string. This is the mechanism for escaping a double quote character,
which is the only character needing escaping in a verbatim string.

## Low Level Grammar Productions {#sec-grammar}

### Identifier Variations

````
Ident = ident
````
The ``Ident`` non-terminal is just an ``ident`` token and represents an ordinary
identifier.

````
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
  underscores matter, so 10 is different from 1_0 and from 010.
* `m.requires` is used to denote the precondition for method m.
* `m.reads` is used to denote the things that method m may read.

````
NoUSIdent = ident - "_" { idChar }
````
A ``NoUSIdent`` is an identifier except that identifiers with a **leading**
underscore are not allowed. The names of user-defined entities are
required to be ``NoUSIdent``s. We introduce more mnemonic names
for these below (e.g. ``ClassName``).

````
WildIdent = NoUSIdent | "_"
````
Identifier, disallowing leading underscores, except the "wildcard"
identifier `_`. When `_` appears it is replaced by a unique generated
identifier distinct from user identifiers. This wildcard has several uses
in the language, but it is not used as part of expressions.

### NoUSIdent Synonyms
In the productions for the declaration of user-defined entities the name of the
user-defined entity is required to be an identifier that does not start
with an underscore, i.e., a ``NoUSIdent``. To make the productions more
mnemonic, we introduce the following synonyms for ``NoUSIdent``.

````
ModuleName = NoUSIdent
ClassName = NoUSIdent
TraitName = NoUSIdent
DatatypeName = NoUSIdent
DatatypeMemberName = NoUSIdent
NewtypeName = NoUSIdent
NumericTypeName = NoUSIdent
SynonymTypeName = NoUSIdent
IteratorName = NoUSIdent
TypeVariableName = NoUSIdent
MethodName = NoUSIdent
FunctionName = NoUSIdent
PredicateName = NoUSIdent
CopredicateName = NoUSIdent
LabelName = NoUSIdent
AttributeName = NoUSIdent
FieldIdent = NoUSIdent
````
A ``FieldIdent`` is one of the ways to identify a field. The other is
using digits.

### Qualified Names
A qualified name starts with the name of the top-level entity and then is followed by
zero or more ``DotSuffix``s which denote a component. Examples:

* `Module.MyType1`
* `MyTuple.1`
* `MyMethod.requires`

The grammar does not actually have a production for qualified names
except in the special case of a qualified name that is known to be
a module name, i.e. a ``QualifiedModuleName``.

### Identifier-Type Combinations
In this section, we describe some nonterminals that combine an identifier and a type.

````
IdentType = WildIdent ":" Type
````
In Dafny, a variable or field is typically declared by giving its name followed by
a ``colon`` and its type. An ``IdentType`` is such a construct.

````
GIdentType(allowGhostKeyword) = [ "ghost" ] IdentType
````
A ``GIdentType`` is a typed entity declaration optionally preceded by `ghost`. The _ghost_
qualifier means the entity is only used during verification and not in the generated code.
Ghost variables are useful for abstractly representing internal state in specifications.
If `allowGhostKeyword` is false then `ghost` is not allowed.

````
LocalIdentTypeOptional = WildIdent [ ":" Type ]
````
A ``LocalIdentTypeOptional`` is used when declaring local variables. 
If a value is specified for the variable, the
type may be omitted because it can be inferred from the initial value.
The initial value value may also be omitted.

````
IdentTypeOptional = WildIdent [ ":" Type ]
````
A ``IdentTypeOptional`` is typically used in a context where the type of the identifier
may be inferred from the context. Examples are in pattern matching or quantifiers.

````
TypeIdentOptional = [ "ghost" ] ( NoUSIdent | digits ) ":" ] Type
````
``TypeIdentOptional``s are used in ``FormalsOptionalIds``. This represents situations
where a type is given but there may not be an identifier.

````
FormalsOptionalIds = "(" [TypeIdentOptional  { "," TypeIdentOptional } ] ")"
````
A ``FormalsOptionalIds`` is a formal parameter list in which the types are required
but the names of the parameters are optional. This is used in algebraic
datatype definitions.

### Numeric Literals
````
Nat = ( digits | hexdigits )
````
A ``Nat`` represents a natural number expressed in either decimal or hexadecimal.

````
Dec = decimaldigits
````
A ``Dec`` represents a decimal fraction literal.


