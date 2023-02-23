# 17. Dafny Grammar {#sec-grammar-details}

The Dafny grammar has a traditional structure: a scanner tokenizes the textual input into a sequence of tokens; the parser consumes the tokens
to produce an AST. The AST is then passed on for name and type resolution and further processing.

Dafny uses the Coco/R lexer and parser generator for its lexer and parser
(<http://www.ssw.uni-linz.ac.at/Research/Projects/Coco>)[@Linz:Coco].
See the [Coco/R Reference
manual](http://www.ssw.uni-linz.ac.at/Research/Projects/Coco/Doc/UserManual.pdf)
for details.
The Dafny input file to Coco/R is the `Dafny.atg` file in the source tree.

The grammar is an _attributed extended BNF_ grammar.
The _attributed_ adjective indicates that the BNF productions are
parameterized by boolean parameters that control variations of the 
production rules, such as whether a particular alternative is permitted or
not. Using such attributes allows combining non-terminals with quite
similar production rules, making a simpler, more compact and more
readable grammer.

The grammar rules presented here replicate those in the source
code, but omit semantic actions, error recovery markers, and
conflict resolution syntax. Some uses of the attribute
parameters are described informally.

The names of character sets and tokens start with a lower case
letter; the names of grammar non-terminals start with
an upper-case letter.




## 17.1. Dafny Syntax

This section gives the definitions of Dafny tokens.

### 17.1.1. Classes of characters

These definitions define some names as representing subsets of the set of characters. Here,

* double quotes enclose the set of characters constituting the class, 
* single quotes enclose a single character (perhaps an escaped representation using `\`), 
* the binary `+` indicates set union, 
* binary `-` indicates set difference, and 
* `ANY` indicates the set of all (unicode) characters.

````grammar
letter = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"

digit = "0123456789"
posDigit = "123456789"
posDigitFrom2 = "23456789"

hexdigit = "0123456789ABCDEFabcdef"

special = "'_?"

cr        = '\r'

lf        = '\n'

tab       = '\t'

space     = ' '

nondigitIdChar = letter + special

idchar = nondigitIdChar + digit

nonidchar = ANY - idchar

charChar = ANY - '\'' - '\\' - cr - lf

stringChar = ANY - '"' - '\\' - cr - lf

verbatimStringChar = ANY - '"'
````

A `nonidchar` is any character except those that can be used in an identifier.
Here the scanner generator will interpret `ANY` as any unicode character.
However, `nonidchar` is used only to mark the end of the `!in` token;
in this context any character other than [whitespace or printable ASCII](#sec-unicode)
will trigger a subsequent scanning or parsing error.

### 17.1.2. Definitions of tokens {#sec-g-tokens}

These definitions use 

* double-quotes to indicate a verbatim string (with no escaping of characters)
* `'"'` to indicate a literal double-quote character
* vertical bar to indicate alternatives
* square brackets to indicate an optional part
* curly braces to indicate 0-or-more repetitions
* parentheses to indicate grouping
* a `-` sign to indicate set difference: any character sequence matched by the left operand except character sequences matched by the right operand
* a sequence of any of the above to indicate concatenation without whitespace

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
    "object" | "object?" | "old" | "opaque" | "opened" | "ORDINAL"
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

ident = nondigitIdChar { idchar } - charToken - reservedword

digits = digit {["_"] digit}

hexdigits = "0x" hexdigit {["_"] hexdigit}

decimaldigits = digit {["_"] digit} '.' digit {["_"] digit}

escapedChar =
    ( "\'" | "\"" | "\\" | "\0" | "\n" | "\r" | "\t"
      | "\u" hexdigit hexdigit hexdigit hexdigit
      | "\U{" hexdigit { hexdigit } "}"
    )

charToken = "'" ( charChar | escapedChar ) "'"

stringToken =
    '"' { stringChar | escapedChar }  '"'
  | "@" '"' { verbatimStringChar | '"' '"' } '"'

ellipsis = "..."
````

There are a few words that have a special meaning in certain contexts, but are not 
reserved words and can be used as identifiers outside of those contexts:

* `least` and `greatest` are recognized as adjectives to the keyword `predicate` (cf. [Section 12.4](#sec-extreme)).
* `older` is a modifier for parameters of non-extreme predicates (cf. [Section 6.4.6](#sec-older-parameters)).

The `\uXXXX` form of an `escapedChar` is only used when the option `--unicode-char=false` is set (which is the default for Dafny 3.x);
the `\U{XXXXXX}` form of an `escapedChar` is only used when the option `--unicode-char=true` is set (which is the default for Dafny 4.x).

## 17.2. Dafny Grammar productions

The grammar productions are presented in the following Extended BNF syntax:

* identifiers starting with a lower case letter denote
terminal symbols (tokens) as defined in the [previous subsection](#sec-g-tokens)
* identifiers starting with an upper case letter denote nonterminal
symbols
* strings (a sequence of characters enclosed by double quote characters)
denote the sequence of enclosed characters
* `=` separates the sides of a production, e.g. `A = a b c`
* `|` separates alternatives, e.g. `a b | c | d e` means `a b` or `c` or `d e`
* `(` `)` groups alternatives, e.g. `(a | b) c` means `a c` or `b c`
* `[ ]` option, e.g. `[a] b` means `a b` or `b`
* `{ }` iteration (0 or more times), e.g. `{a} b` means `b` or `a b` or `a a b` or ...
* We allow `|` inside `[ ]` and `{ }`. So `[a | b]` is short for `[(a | b)]`
  and `{a | b}` is short for `{(a | b)}`.
* `//` in a line introduces a comment that extends to the end-of-the line, but does not terminate the production
* The first production defines the name of the grammar, in this case `Dafny`.

In addition to the Coco rules, for the sake of readability we have adopted
these additional conventions.

* We allow `-` to be used. `a - b` means it matches if it matches `a` but not `b`.
* We omit the `.` that marks the end of a CoCo/R production.
* we omit deprecated features.

To aid in explaining the grammar we have added some additional productions
that are not present in the original grammar. We name these with a trailing
underscore. Inlining these where they are referenced will reconstruct the original grammar.

<!-- A note on formatting the sections below: LaTex 
### 17.2.1. Programs {#g-program}
([discussion](#sec-program)) 

````grammar
Dafny = { IncludeDirective_ } { TopDecl(isTopLevel:true, isAbstract: false) } EOF
````


#### 17.2.1.1. Include directives {#g-include-directive}
([discussion](#sec-include-directive))

````grammar
IncludeDirective_ = "include" stringToken
````

#### 17.2.1.2. Top-level declarations {#g-top-level-declaration}
([discussion](#sec-top-level-declaration))

````grammar
TopDecl(isTopLevel, isAbstract) =
  { DeclModifier }
  ( SubModuleDecl(isTopLevel)
  | ClassDecl
  | DatatypeDecl
  | NewtypeDecl
  | SynonymTypeDecl  // includes opaque types
  | IteratorDecl
  | TraitDecl
  | ClassMemberDecl(allowConstructors: false, isValueType: true, moduleLevelDecl: true)
  )
````

#### 17.2.1.3. Declaration modifiers {#g-declaration-modifier}
([discussion](#sec-declaration-modifier)) 

````grammar
DeclModifier = ( "abstract" | "ghost" | "static" | "opaque" )
````

### 17.2.2. Modules {#g-module}

````grammar
SubModuleDecl(isTopLevel) = ( ModuleDefinition | ModuleImport | ModuleExport )
````

Module export declarations are not permitted if `isTopLevel` is true.

#### 17.2.2.1. Module Definitions {#g-module-definition}
([discussion](#sec-module-definition)) 

````grammar
ModuleDefinition(isTopLevel) = 
  "module" { Attribute } ModuleQualifiedName
  [ "refines" ModuleQualifiedName ]
  "{" { TopDecl(isTopLevel:false, isAbstract) } "}"
````

The `isAbstract` argument is true if the preceding `DeclModifiers` include "abstract".

#### 17.2.2.2. Module Imports {#g-module-import}
([discussion](#sec-importing-modules)) 

````grammar
ModuleImport =
  "import"
  [ "opened" ]
  ( QualifiedModuleExport
  | ModuleName "=" QualifiedModuleExport
  | ModuleName ":" QualifiedModuleExport
  )

QualifiedModuleExport =
    ModuleQualifiedName [ "`" ModuleExportSuffix ]

ModuleExportSuffix =
  ( ExportId
  | "{" ExportId { "," ExportId } "}"
  )
````

#### 17.2.2.3. Module Export Definitions {#g-module-export}
([discussion](#sec-export-sets)) 

````grammar
ModuleExport =
  "export"
  [ ExportId ]
  [ "..." ]
  {
    "extends"  ExportId { "," ExportId }
  | "provides" ( ExportSignature { "," ExportSignature } | "*" )
  | "reveals"  ( ExportSignature { "," ExportSignature } | "*" )
  }

ExportSignature = TypeNameOrCtorSuffix [ "." TypeNameOrCtorSuffix ]
````

### 17.2.3. Types {#g-type}
([discussion](#sec-types)) 

````grammar
Type = DomainType_ | ArrowType_

DomainType_ =
  ( BoolType_ | CharType_ | IntType_ | RealType_
  | OrdinalType_ | BitVectorType_ | ObjectType_
  | FiniteSetType_ | InfiniteSetType_
  | MultisetType_
  | FiniteMapType_ | InfiniteMapType_
  | SequenceType_
  | NatType_
  | StringType_
  | ArrayType_
  | TupleType
  | NamedType
  )

NamedType = NameSegmentForTypeName { "." NameSegmentForTypeName }

NameSegmentForTypeName = Ident [ GenericInstantiation ]
````


#### 17.2.3.1. Basic types {#g-basic-type}
([discussion](#sec-basic-type)) 

````grammar
BoolType_ = "bool"
IntType_ = "int"
RealType_ = "real"
BitVectorType_ = bvToken
OrdinalType_ = "ORDINAL"
CharType_ = "char"
````


#### 17.2.3.2. Generic instantiation {#g-generic-instantiation}
([discussion](#sec-generic-instantiation)) 

````grammar
GenericInstantiation = "<" Type { "," Type } ">"
````

#### 17.2.3.3. Type parameter {#g-type-parameter}
([discussion](#sec-type-parameters)) 

````grammar
GenericParameters(allowVariance) =
  "<" [ Variance ] TypeVariableName { TypeParameterCharacteristics }
  { "," [ Variance ] TypeVariableName { TypeParameterCharacteristics } }
  ">"

// The optional Variance indicator is permitted only if allowVariance is true
Variance = ( "*" | "+" | "!" | "-" )

TypeParameterCharacteristics = "(" TPCharOption { "," TPCharOption } ")"

TPCharOption = ( "==" | "0" | "00" | "!" "new" )
````

#### 17.2.3.4. Collection types {#g-collection-type}
([discussion](#sec-collection-types)) 

````grammar
FiniteSetType_ = "set" [ GenericInstantiation ]

InfiniteSetType_ = "iset" [ GenericInstantiation ]

MultisetType_ = "multiset" [ GenericInstantiation ]

SequenceType_ = "seq" [ GenericInstantiation ]

StringType_ = "string"

FiniteMapType_ = "map" [ GenericInstantiation ]

InfiniteMapType_ = "imap" [ GenericInstantiation ]
````

#### 17.2.3.5. Type definitions {#g-type-definition}
([discussion](#sec-type-definition)) 

````grammar
SynonymTypeDecl =
  SynonymTypeDecl_ | OpaqueTypeDecl_ | SubsetTypeDecl_

SynonymTypeName = NoUSIdent

SynonymTypeDecl_ =
  "type" { Attribute } SynonymTypeName
   { TypeParameterCharacteristics }
   [ GenericParameters ]
   "=" Type

OpaqueTypeDecl_ =
  "type" { Attribute } SynonymTypeName
   { TypeParameterCharacteristics }
   [ GenericParameters ]
   [ TypeMembers ]

TypeMembers =
  "{"
  {
    { DeclModifier }
    ClassMemberDecl(allowConstructors: false,
                    isValueType: true,
                    moduleLevelDecl: false,
                    isWithinAbstractModule: module.IsAbstract)
  }
  "}"

SubsetTypeDecl_ =
  "type"
  { Attribute }
  SynonymTypeName [ GenericParameters ]
  "="
  LocalIdentTypeOptional
  "|"
  Expression(allowLemma: false, allowLambda: true)
  [ "ghost" "witness" Expression(allowLemma: false, allowLambda: true)
  | "witness" Expression((allowLemma: false, allowLambda: true)
  | "witness" "*"
  ]

NatType_ = "nat"

NewtypeDecl = "newtype" { Attribute } NewtypeName "="
  [ ellipsis ]
  ( LocalIdentTypeOptional
    "|"
    Expression(allowLemma: false, allowLambda: true)
    [ "ghost" "witness" Expression(allowLemma: false, allowLambda: true)
    | "witness" Expression((allowLemma: false, allowLambda: true)
    | "witness" "*"
    ]
  | Type
  )
  [ TypeMembers ]
````


#### 17.2.3.6. Class type {#g-class-type}
([discussion](#sec-class-types)) 

````grammar
ClassDecl = "class" { Attribute } ClassName [ GenericParameters ]
  ["extends" Type {"," Type} | ellipsis ]
  "{" { { DeclModifier }
        ClassMemberDecl(modifiers,
                        allowConstructors: true,
                        isValueType: false,
                        moduleLevelDecl: false) 
      }
  "}"

ClassMemberDecl(modifiers, allowConstructors, isValueType, moduleLevelDecl) =
  ( FieldDecl(isValueType) // allowed iff moduleLevelDecl is false
  | ConstantFieldDecl(moduleLevelDecl)
  | FunctionDecl(isWithinAbstractModule)
  | MethodDecl(modifiers, allowConstructors)
  )
````


#### 17.2.3.7. Trait types {#g-trait-type}
([discussion](#sec-trait-types)) 

````grammar
TraitDecl =
  "trait" { Attribute } ClassName [ GenericParameters ]
  [ "extends" Type { "," Type } | ellipsis ]
  "{"
   { { DeclModifier } ClassMemberDecl(allowConstructors: true,
                                      isValueType: false,
                                      moduleLevelDecl: false,
                                      isWithinAbstractModule: false) }
  "}"
````

#### 17.2.3.8. Object type {#g-object-type}
([discussion](#sec-object-type)) 

````grammar
ObjectType_ = "object" | "object?"
````

#### 17.2.3.9. Array types {#g-array-type}
([discussion](#sec-array-type)) 

````grammar
ArrayType_ = arrayToken [ GenericInstantiation ]
````

#### 17.2.3.10. Iterator types {#g-iterator-type}
([discussion](#sec-iterator-types)) 

````grammar
IteratorDecl = "iterator" { Attribute } IteratorName
  ( [ GenericParameters ]
    Formals(allowGhostKeyword: true, allowNewKeyword: false, 
                                     allowOlderKeyword: false)
    [ "yields" Formals(allowGhostKeyword: true, allowNewKeyword: false, 
                                                allowOlderKeyword: false) ]
  | ellipsis
  )
  IteratorSpec
  [ BlockStmt ]
````

#### 17.2.3.11. Arrow types {#g-arrow-type}
([discussion](#sec-arrow-types)) 

````grammar
ArrowType_ = ( DomainType_ "~>" Type
             | DomainType_ "-->" Type
             | DomainType_ "->" Type
             )
````

#### 17.2.3.12. Algebraic datatypes {#g-datatype}
([discussion](#sec-datatype)) 

````grammar
DatatypeDecl =
  ( "datatype" | "codatatype" )
  { Attribute }
  DatatypeName [ GenericParameters ]
  "=" 
  [ ellipsis ]
  [ "|" ] DatatypeMemberDecl
  { "|" DatatypeMemberDecl }
  [ TypeMembers ]

DatatypeMemberDecl =
  { Attribute } DatatypeMemberName [ FormalsOptionalIds ]
````

### 17.2.4. Type member declarations {#g-member-declaration}
([discussion](#sec-member-declaration)) 

#### 17.2.4.1. Fields {#g-field-declaration}
([discussion](#sec-field-declaration)) 

````grammar
FieldDecl(isValueType) =
  "var" { Attribute } FIdentType { "," FIdentType }
````

A `FieldDecl` is not permitted if `isValueType` is true.

#### 17.2.4.2. Constant fields {#g-const-declaration}
([discussion](#sec-constant-field-declaration)) 

````grammar
ConstantFieldDecl(moduleLevelDecl) =
  "const" { Attribute } CIdentType [ ellipsis ]
   [ ":=" Expression(allowLemma: false, allowLambda:true) ]
````

If `moduleLevelDecl` is true, then the `static` modifier is not permitted
(the constant field is static implicitly).

#### 17.2.4.3. Method declarations {#g-method-declaration}
([discussion](#sec-method-declaration)) 

````grammar
MethodDecl(isGhost, allowConstructors, isWithinAbstractModule) =
  MethodKeyword_ { Attribute } [ MethodFunctionName ]
  ( MethodSignature_(isGhost, isExtreme: true iff this is a least
                                   or greatest lemma declaration)
  | ellipsis
  )
  MethodSpec(isConstructor: true iff this is a constructor declaration)
  [ BlockStmt ]

MethodKeyword_ = ( "method"
                 | "constructor"
                 | "lemma"
                 | "twostate" "lemma"
                 | "least" "lemma"
                 | "greatest" "lemma"
                 )


MethodSignature_(isGhost, isExtreme) =
  [ GenericParameters ]
  [ KType ]    // permitted only if isExtreme == true
  Formals(allowGhostKeyword: !isGhost, allowNewKeyword: isTwostateLemma, 
          allowOlderKeyword: false, allowDefault: true)
  [ "returns" Formals(allowGhostKeyword: !isGhost, allowNewKeyword: false, 
                      allowOlderKeyword: false, allowDefault: false) ]

KType = "[" ( "nat" | "ORDINAL" ) "]"

Formals(allowGhostKeyword, allowNewKeyword, allowOlderKeyword, allowDefault) =
  "(" [ GIdentType(allowGhostKeyword, allowNewKeyword, allowOlderKeyword, 
                   allowNameOnlyKeyword: true, allowDefault)
        { "," GIdentType(allowGhostKeyword, allowNewKeyword, allowOlderKeyword,
                         allowNameOnlyKeyword: true, allowDefault) }
      ]
  ")"
````

If `isWithinAbstractModule` is false, then the method must have
a body for the program that contains the declaration to be compiled.

The `KType` may be specified only for least and greatest lemmas.

#### 17.2.4.4. Function declarations {#g-function-declaration}
([discussion](#sec-function-declaration)) 

````grammar
FunctionDecl(isWithinAbstractModule) =
  ( [ "twostate" ] "function" [ "method" ] { Attribute }
    MethodFunctionName
    FunctionSignatureOrEllipsis_(allowGhostKeyword:
                                           ("method" present),
                                 allowNewKeyword:
                                           "twostate" present)
  | "predicate" [ "method" ] { Attribute }
    MethodFunctionName
    PredicateSignatureOrEllipsis_(allowGhostKeyword:
                                           ("method" present),
                                  allowNewKeyword:
                                           "twostate" present,
                                  allowOlderKeyword: true)
  | ( "least" | "greatest" ) "predicate" { Attribute }
    MethodFunctionName
    PredicateSignatureOrEllipsis_(allowGhostKeyword: false,
                         allowNewKeyword: "twostate" present,
                         allowOlderKeyword: false))
  )
  FunctionSpec
  [ FunctionBody ]

FunctionSignatureOrEllipsis_(allowGhostKeyword) =
  FunctionSignature_(allowGhostKeyword) | ellipsis

FunctionSignature_(allowGhostKeyword, allowNewKeyword) =
  [ GenericParameters ]
  Formals(allowGhostKeyword, allowNewKeyword, allowOlderKeyword: true, 
          allowDefault: true)
  ":"
  ( Type
  | "(" GIdentType(allowGhostKeyword: false,
                   allowNewKeyword: false,
                   allowOlderKeyword: false,
                   allowNameOnlyKeyword: false,
                   allowDefault: false)
    ")"
  )

PredicateSignatureOrEllipsis_(allowGhostKeyword, allowNewKeyword, 
                              allowOlderKeyword) =
    PredicateSignature_(allowGhostKeyword, allowNewKeyword, allowOlderKeyword) 
  | ellipsis

PredicateSignature_(allowGhostKeyword, allowNewKeyword, allowOlderKeyword) =
  [ GenericParameters ]
  [ KType ]
  Formals(allowGhostKeyword, allowNewKeyword, allowOlderKeyword, 
          allowDefault: true)
  [
    ":"
    ( Type
    | "(" Ident ":" "bool" ")"
    )
  ]

FunctionBody = "{" Expression(allowLemma: true, allowLambda: true)
               "}" [ "by" "method" BlockStmt ]
````

### 17.2.5. Specifications

#### 17.2.5.1. Method specifications {#g-method-specification}
([discussion](#sec-method-specification)) 

````grammar
MethodSpec =
  { ModifiesClause(allowLambda: false)
  | RequiresClause(allowLabel: true)
  | EnsuresClause(allowLambda: false)
  | DecreasesClause(allowWildcard: true, allowLambda: false)
  }
````

#### 17.2.5.2. Function specifications {#g-function-specification}
([discussion](#sec-function-specification)) 

````grammar
FunctionSpec =
  { RequiresClause(allowLabel: true)
  | ReadsClause(allowLemma: false, allowLambda: false, allowWild: true)
  | EnsuresClause(allowLambda: false)
  | DecreasesClause(allowWildcard: false, allowLambda: false)
  }
````

#### 17.2.5.3. Lambda function specifications {#g-lambda-specification}
([discussion](#sec-lambda-specification)) 

````grammar
LambdaSpec =
  { ReadsClause(allowLemma: true, allowLambda: false, allowWild: true)
  | "requires" Expression(allowLemma: false, allowLambda: false)
  }
````

#### 17.2.5.4. Iterator specifications {#g-iterator-specification}
([discussion](#sec-iterator-specification)) 

````grammar
IteratorSpec =
  { ReadsClause(allowLemma: false, allowLambda: false,
                                  allowWild: false)
  | ModifiesClause(allowLambda: false)
  | [ "yield" ] RequiresClause(allowLabel: !isYield)
  | [ "yield" ] EnsuresClause(allowLambda: false)
  | DecreasesClause(allowWildcard: false, allowLambda: false)
  }
````

#### 17.2.5.5. Loop specifications {#g-loop-specification}
([discussion](#sec-loop-specification)) 

````grammar
LoopSpec =
  { InvariantClause_
  | DecreasesClause(allowWildcard: true, allowLambda: true)
  | ModifiesClause(allowLambda: true)
  }
````

#### 17.2.5.6. Requires clauses {#g-requires-clause}
([discussion](#sec-requires-clause)) 

````grammar
RequiresClause(allowLabel) =
  "requires" { Attribute }
  [ LabelName ":" ]  // Label allowed only if allowLabel is true
  Expression(allowLemma: false, allowLambda: false)
````

#### 17.2.5.7. Ensures clauses {#g-ensures-clause}
([discussion](#sec-ensures-clause)) 

````grammar
EnsuresClause(allowLambda) =
  "ensures" { Attribute } Expression(allowLemma: false, allowLambda)
````

#### 17.2.5.8. Decreases clauses {#g-decreases-clause}
([discussion](#sec-decreases-clause)) 

````grammar
DecreasesClause(allowWildcard, allowLambda) =
  "decreases" { Attribute } DecreasesList(allowWildcard, allowLambda)

DecreasesList(allowWildcard, allowLambda) =
  PossiblyWildExpression(allowLambda, allowWildcard)
  { "," PossiblyWildExpression(allowLambda, allowWildcard) }

PossiblyWildExpression(allowLambda, allowWild) =
  ( "*"  // if allowWild is false, using '*' provokes an error
  | Expression(allowLemma: false, allowLambda)
  )
````

#### 17.2.5.9. Modifies clauses {#g-modifies-clause}
([discussion](#sec-modifies-clause)) 

````grammar
ModifiesClause(allowLambda) =
  "modifies" { Attribute }
  FrameExpression(allowLemma: false, allowLambda)
  { "," FrameExpression(allowLemma: false, allowLambda) }
````

#### 17.2.5.10. Invariant clauses {#g-invariant-clause}
([discussion](#sec-invariant-clause)) 

````grammar
InvariantClause_ =
  "invariant" { Attribute }
  Expression(allowLemma: false, allowLambda: true)
````

#### 17.2.5.11. Reads clauses {#g-reads-clause}
([discussion](#sec-reads-clause)) 

````grammar
ReadsClause(allowLemma, allowLambda, allowWild) =
  "reads"
  { Attribute }
  PossiblyWildFrameExpression(allowLemma, allowLambda, allowWild)
  { "," PossiblyWildFrameExpression(allowLemma, allowLambda, allowWild) }
````

#### 17.2.5.12. Frame expressions {#g-frame-expression}
([discussion](#sec-frame-expression)) 

````grammar
FrameExpression(allowLemma, allowLambda) =
  ( Expression(allowLemma, allowLambda) [ FrameField ]
  | FrameField
  )

FrameField = "`" IdentOrDigits

PossiblyWildFrameExpression(allowLemma, allowLambda, allowWild) =
  ( "*"  // error if !allowWild and '*'
  | FrameExpression(allowLemma, allowLambda)
  )
````

### 17.2.6. Statements {#g-statement}

#### 17.2.6.1. Labeled statement {#g-labeled-statement}

([discussion](#sec-labeled-statement)) 

````grammar
Stmt = { "label" LabelName ":" } NonLabeledStmt
````

#### 17.2.6.2. Non-Labeled statement {#g-nonlabeled-statement}

([discussion](#sec-statements)) 

````grammar
NonLabeledStmt =
  ( AssertStmt | AssumeStmt | BlockStmt | BreakStmt
  | CalcStmt | ExpectStmt | ForallStmt | IfStmt
  | MatchStmt | ModifyStmt
  | PrintStmt | ReturnStmt | RevealStmt
  | UpdateStmt | UpdateFailureStmt
  | VarDeclStatement | WhileStmt | ForLoopStmt | YieldStmt
  )
````

#### 17.2.6.3. Break and continue statements {#g-break-continue-statement}

([discussion](#sec-break-continue-statement)) 

````grammar
BreakStmt =
  ( "break" LabelName ";"
  | "continue" LabelName ";"
  | { "break" } "break" ";"
  | { "break" } "continue" ";"
  )
````

#### 17.2.6.4. Block statement {#g-block-statement}

([discussion](#sec-block-statement)) 

````grammar
BlockStmt = "{" { Stmt } "}"
````

#### 17.2.6.5. Return statement {#g-return-statement}

([discussion](#sec-return-statement)) 

````grammar
ReturnStmt = "return" [ Rhs { "," Rhs } ] ";"
````

#### 17.2.6.6. Yield statement {#g-yield-statement}

([discussion](#sec-yield-statement)) 

````grammar
YieldStmt = "yield" [ Rhs { "," Rhs } ] ";"
````

#### 17.2.6.7. Update and call statement {#g-update-and-call-statement}

([discussion](#sec-update-and-call-statement)) 

````grammar
UpdateStmt =
  Lhs
  ( {Attribute} ";"
  |
    { "," Lhs }
    ( ":=" Rhs { "," Rhs }
    | ":|" [ "assume" ]
               Expression(allowLemma: false, allowLambda: true)
    )
    ";"
  )
````

#### 17.2.6.8. Update with failure statement {#g-update-with-failure-statement}

([discussion](#sec-update-with-failure-statement)) 

````grammar
UpdateFailureStmt  =
  [ Lhs { "," Lhs } ]
  ":-"
  [ "expect"  | "assert" | "assume" ]
  Expression(allowLemma: false, allowLambda: false)
  { "," Rhs }
  ";"
````

#### 17.2.6.9. Variable declaration statement {#g-variable-declaration-statement}

([discussion](#sec-variable-declaration-statement)) 

````grammar
VarDeclStatement =
  [ "ghost" ] "var" { Attribute }
  (
    LocalIdentTypeOptional
    { "," { Attribute } LocalIdentTypeOptional }
    [ ":="
      Rhs { "," Rhs }
    | ":-"
      [ "expect" | "assert" | "assume" ]
      Expression(allowLemma: false, allowLambda: false)
      { "," Rhs }
    | { Attribute }
      ":|"
      [ "assume" ] Expression(allowLemma: false, allowLambda: true)
    ]
  |
    CasePatternLocal
    ( ":=" | { Attribute } ":|" )
    Expression(allowLemma: false, allowLambda: true)
  )
  ";"

CasePatternLocal = 
  ( [ Ident ] "(" CasePatternLocal { "," CasePatternLocal } ")"
  | LocalIdentTypeOptional
  )
````

#### 17.2.6.10. Guards {#g-guard}

([discussion](#sec-guard)) 

````grammar
Guard = ( "*"
        | "(" "*" ")"
        | Expression(allowLemma: true, allowLambda: true)
        )
````

#### 17.2.6.11. Binding guards {#g-binding-guard} 

([discussion](#sec-binding-guards))

````grammar
BindingGuard(allowLambda) =
  IdentTypeOptional { "," IdentTypeOptional }
  { Attribute }
  ":|"
  Expression(allowLemma: true, allowLambda)
````

#### 17.2.6.12. If statement {#g-if-statement}

([discussion](#sec-if-statement)) 

````grammar
IfStmt = "if"
  ( AlternativeBlock(allowBindingGuards: true)
  |
    ( BindingGuard(allowLambda: true)
    | Guard
    )
    BlockStmt [ "else" ( IfStmt | BlockStmt ) ]
  )

AlternativeBlock(allowBindingGuards) =
  ( { AlternativeBlockCase(allowBindingGuards) }
  | "{" { AlternativeBlockCase(allowBindingGuards) } "}"
  )

AlternativeBlockCase(allowBindingGuards) =
  { "case"
    (
    BindingGuard(allowLambda: false) //permitted iff allowBindingGuards == true
    | Expression(allowLemma: true, allowLambda: false)
    ) "=>" { Stmt }
  }
````

#### 17.2.6.13. While Statement {#g-while-statement}

([discussion](#sec-while-statement)) 

````grammar
WhileStmt =
  "while"
  ( LoopSpec
    AlternativeBlock(allowBindingGuards: false)
  | Guard
    LoopSpec
    ( BlockStmt
    |           // no body
    )
  )
````

#### 17.2.6.14. For statement {#g-for-statement}

([discussion](#sec-for-statement))

````grammar
ForLoopStmt =
  "for" IdentTypeOptional ":="
  Expression(allowLemma: false, allowLambda: false)
  ( "to" | "downto" )
  ( "*" | Expression(allowLemma: false, allowLambda: false)
  )
  LoopSpec
  ( BlockStmt
  |           // no body
  )
````

#### 17.2.6.15. Match statement {#g-match-statement}

([discussion](#sec-match-statement)) 

````grammar
MatchStmt =
  "match"
  Expression(allowLemma: true, allowLambda: true)
  ( "{" { CaseStmt } "}"
  | { CaseStmt }
  )

CaseStmt = "case" ExtendedPattern "=>" { Stmt }
````

#### 17.2.6.16. Assert statement {#g-assert-statement}

([discussion](#sec-assert-statement)) 

````grammar
AssertStmt =
  "assert"
  { Attribute }
  [ LabelName ":" ]
  Expression(allowLemma: false, allowLambda: true)
  ( ";"
  | "by" BlockStmt
  )
````

#### 17.2.6.17. Assume statement {#g-assume-statement}

([discussion](#sec-assume-statement)) 

````grammar
AssumeStmt =
  "assume"
  { Attribute }
  Expression(allowLemma: false, allowLambda: true)
  ";"
````

#### 17.2.6.18. Expect statement {#g-expect-statement}

([discussion](#sec-expect-statement)) 

````grammar
ExpectStmt =
  "expect"
  { Attribute }
  Expression(allowLemma: false, allowLambda: true)
  [ "," Expression(allowLemma: false, allowLambda: true) ]
  ";"
````

#### 17.2.6.19. Print statement {#g-print-statement}

([discussion](#sec-print-statement)) 

````grammar
PrintStmt =
  "print"
  Expression(allowLemma: false, allowLambda: true)
  { "," Expression(allowLemma: false, allowLambda: true) }
  ";"
````

#### 17.2.6.20. Reveal statement {#g-reveal-statement}

([discussion](#sec-reveal-statement)) 

````grammar
RevealStmt =
  "reveal"
  Expression(allowLemma: false, allowLambda: true)
  { "," Expression(allowLemma: false, allowLambda: true) }
  ";"
````
#### 17.2.6.21. Forall statement {#g-forall-statement}

([discussion](#sec-forall-statement)) 

````grammar
ForallStmt =
  "forall"
  ( "(" [ QuantifierDomain ] ")"
  | [ QuantifierDomain ]
  )
  { EnsuresClause(allowLambda: true) }
  [ BlockStmt ]
````
#### 17.2.6.22. Modify statement {#g-modify-statement}

([discussion](#sec-modify-statement)) 

````grammar
ModifyStmt =
  "modify"
  { Attribute }
  FrameExpression(allowLemma: false, allowLambda: true)
  { "," FrameExpression(allowLemma: false, allowLambda: true) }
  ";"
````

#### 17.2.6.23. Calc statement {#g-calc-statement}

([discussion](#sec-calc-statement)) 

````grammar
CalcStmt = "calc" { Attribute } [ CalcOp ] "{" CalcBody_ "}"

CalcBody_ = { CalcLine_ [ CalcOp ] Hints_ }

CalcLine_ = Expression(allowLemma: false, allowLambda: true) ";"

Hints_ = { ( BlockStmt | CalcStmt ) }

CalcOp =
  ( "==" [ "#" "["
           Expression(allowLemma: true, allowLambda: true) "]" ]
  | "<" | ">"
  | "!=" | "<=" | ">="
  | "<==>" | "==>" | "<=="
  )
````

### 17.2.7. Expressions

#### 17.2.7.1. Top-level expression {#g-top-level-expression}

([discussion](#sec-top-level-expression)) 

````grammar
Expression(allowLemma, allowLambda, allowBitwiseOps = true) =
  EquivExpression(allowLemma, allowLambda, allowBitwiseOps)
  [ ";" Expression(allowLemma, allowLambda, allowBitwiseOps) ]
````

The "allowLemma" argument says whether or not the expression
to be parsed is allowed to have the form `S;E` where `S` is a call to a lemma.
"allowLemma" should be passed in as "false" whenever the expression to
be parsed sits in a context that itself is terminated by a semi-colon.

The "allowLambda" says whether or not the expression to be parsed is
allowed to be a lambda expression.  More precisely, an identifier or
parenthesized, comma-delimited list of identifiers is allowed to
continue as a lambda expression (that is, continue with a `reads`, `requires`,
or `=>`) only if "allowLambda" is true.  This affects function/method/iterator
specifications, if/while statements with guarded alternatives, and expressions
in the specification of a lambda expression itself.

#### 17.2.7.2. Equivalence expression {#g-equivalence-expression}

([discussion](#sec-equivalence-expression)) 

````grammar
EquivExpression(allowLemma, allowLambda, allowBitwiseOps) =
  ImpliesExpliesExpression(allowLemma, allowLambda, allowBitwiseOps)
  { "<==>" ImpliesExpliesExpression(allowLemma, allowLambda, allowBitwiseOps) }
````

#### 17.2.7.3. Implies expression {#g-implies-expression}

([discussion](#sec-implies-expression)) 

````grammar
ImpliesExpliesExpression(allowLemma, allowLambda, allowBitwiseOps) =
  LogicalExpression(allowLemma, allowLambda)
  [ (  "==>" ImpliesExpression(allowLemma, allowLambda, allowBitwiseOps)
    | "<==" LogicalExpression(allowLemma, allowLambda, allowBitwiseOps)
            { "<==" LogicalExpression(allowLemma, allowLambda, allowBitwiseOps) }
    )
  ]

ImpliesExpression(allowLemma, allowLambda, allowBitwiseOps) =
  LogicalExpression(allowLemma, allowLambda, allowBitwiseOps)
  [  "==>" ImpliesExpression(allowLemma, allowLambda, allowBitwiseOps) ]
````

#### 17.2.7.4. Logical expression {#g-logical-expression}

([discussion](#sec-logical-expression)) 

````grammar
LogicalExpression(allowLemma, allowLambda, allowBitwiseOps) =
  [ "&&" | "||" ]
  RelationalExpression(allowLemma, allowLambda, allowBitwiseOps)
  { ( "&&" | "||" )
    RelationalExpression(allowLemma, allowLambda, allowBitwiseOps)
  }
````

#### 17.2.7.5. Relational expression {#g-relational-expression}

([discussion](#sec-relational-expression)) 

````grammar
RelationalExpression(allowLemma, allowLambda, allowBitwiseOps) =
  ShiftTerm(allowLemma, allowLambda, allowBitwiseOps)
  { RelOp ShiftTerm(allowLemma, allowLambda, allowBitwiseOps) }

RelOp =
  ( "=="
    [ "#" "[" Expression(allowLemma: true, allowLambda: true) "]" ]
  | "!="
    [ "#" "[" Expression(allowLemma: true, allowLambda: true) "]" ]
  | "<" | ">" | "<=" | ">="
  | "in"
  | "!in"
  | "!!"
  )
````

#### 17.2.7.6. Bit-shift expression {#g-bit-shift-expression}

([discussion](#sec-bit-shift-expression)) 

````grammar
ShiftTerm(allowLemma, allowLambda, allowBitwiseOps) =
  Term(allowLemma, allowLambda, allowBitwiseOps)
  { ShiftOp Term(allowLemma, allowLambda, allowBitwiseOps) }

ShiftOp = ( "<<" | ">>" )
````

#### 17.2.7.7. Term (addition operations) {#g-term}

([discussion](#sec-addition-expression)) 

````grammar
Term(allowLemma, allowLambda, allowBitwiseOps) =
  Factor(allowLemma, allowLambda, allowBitwiseOps)
  { AddOp Factor(allowLemma, allowLambda, allowBitwiseOps) }

AddOp = ( "+" | "-" )
````

#### 17.2.7.8. Factor (multiplication operations) {#g-factor}

([discussion](#sec-multiplication-expression)) 

````grammar
Factor(allowLemma, allowLambda, allowBitwiseOps) =
  BitvectorFactor(allowLemma, allowLambda, allowBitwiseOps)
  { MulOp BitvectorFactor(allowLemma, allowLambda, allowBitwiseOps) }

MulOp = ( "*" | "/" | "%" )
````

#### 17.2.7.9. Bit-vector expression {#g-bit-vector-expression}
([discussion](#sec-bitvector-expression)) 

````grammar
BitvectorFactor(allowLemma, allowLambda, allowBitwiseOps) =
  AsExpression(allowLemma, allowLambda, allowBitwiseOps)
  { BVOp AsExpression(allowLemma, allowLambda, allowBitwiseOps) }

BVOp = ( "|" | "&" | "^" )
````

If `allowBitwiseOps` is false, it is an error to have a bitvector operation.

#### 17.2.7.10. As/Is expression {#g-as-is-expression}
([discussion](#sec-as-is-expression)) 

````grammar
AsExpression(allowLemma, allowLambda, allowBitwiseOps) =
  UnaryExpression(allowLemma, allowLambda, allowBitwiseOps)
  { ( "as" | "is" ) Type }
````

#### 17.2.7.11. Unary expression {#g-unary-expression}
([discussion](#sec-unary-expression)) 

````grammar
UnaryExpression(allowLemma, allowLambda, allowBitwiseOps) =
  ( "-" UnaryExpression(allowLemma, allowLambda, allowBitwiseOps)
  | "!" UnaryExpression(allowLemma, allowLambda, allowBitwiseOps)
  | PrimaryExpression(allowLemma, allowLambda, allowBitwiseOps)
  )
````

#### 17.2.7.12. Primary expression {#g-primary-expression}
([discussion](#sec-primary-expression)) 

````grammar
PrimaryExpression(allowLemma, allowLambda, allowBitwiseOps) =
  ( NameSegment { Suffix }
  | LambdaExpression(allowLemma, allowBitwiseOps)
  | MapDisplayExpr { Suffix }
  | SeqDisplayExpr { Suffix }
  | SetDisplayExpr { Suffix }
  | EndlessExpression(allowLemma, allowLambda, allowBitwiseOps)
  | ConstAtomExpression { Suffix }
  )
````

#### 17.2.7.13. Lambda expression {#g-lambda-expression}
([discussion](#sec-lambda-expression)) 

````grammar
LambdaExpression(allowLemma, allowBitwiseOps) =
  ( WildIdent
  | "(" [ IdentTypeOptional { "," IdentTypeOptional } ] ")"
  )
  LambdaSpec
  "=>"
  Expression(allowLemma, allowLambda: true, allowBitwiseOps)
````

#### 17.2.7.14. Left-hand-side expression #g-lhs-expression}
([discussion](#sec-lhs-expression)) {

````grammar
Lhs =
  ( NameSegment { Suffix }
  | ConstAtomExpression Suffix { Suffix }
  )
````

#### 17.2.7.15. Right-hand-side expression {#g-rhs-expression}
([discussion](#sec-rhs-expression)) 

````grammar
Rhs =
    ArrayAllocation
  | ObjectAllocation_
  | Expression(allowLemma: false, allowLambda: true, allowBitwiseOps: true)
  | HavocRhs_
  )
  { Attribute }
</pre>

#### 17.2.7.16. Array allocation right-hand-side expression {#g-array-allocation-expression}
([discussion](#sec-array-allocation)) 

````grammar
ArrayAllocation_ =
  "new" [ Type ] "[" [ Expressions ] "]"
  [ "(" Expression(allowLemma: true, allowLambda: true) ")"
  | "[" [ Expressions ] "]"
  ]
````

#### 17.2.7.17. Object allocation right-hand-side expression {#g-object-allocation-expression}
([discussion](#sec-object-allocation)) 

````grammar
ObjectAllocation_ = "new" Type [ "." TypeNameOrCtorSuffix ]
                               [ "(" [ Bindings ] ")" ]
````

#### 17.2.7.18. Havoc right-hand-side expression {#g-havoc-expression}
([discussion](#sec-havoc-expression)) 

````grammar
HavocRhs_ = "*"
````

#### 17.2.7.19. Atomic expressions {#g-atomic-expression}
([discussion](#sec-atomic-expression)) 

````grammar
ConstAtomExpression =
  ( LiteralExpression
  | ThisExpression_
  | FreshExpression_
  | AllocatedExpression_
  | UnchangedExpression_
  | OldExpression_
  | CardinalityExpression_
  | ParensExpression
  )
````

#### 17.2.7.20. Literal expressions {#g-literal-expression}
([discussion](#sec-literal-expression)) 

````grammar
LiteralExpression =
 ( "false" | "true" | "null" | Nat | Dec |
   charToken | stringToken )

Nat = ( digits | hexdigits )

Dec = decimaldigits
````

#### 17.2.7.21. This expression {#g-this-expression}
([discussion](#sec-this-expression)) 

````grammar
ThisExpression_ = "this"
````

#### 17.2.7.22. Old and Old@ Expressions {#g-old-expression}
([discussion](#sec-old-expression)) 

````grammar
OldExpression_ =
  "old" [ "@" LabelName ]
  "(" Expression(allowLemma: true, allowLambda: true) ")"
````

#### 17.2.7.23. Fresh Expressions {#g-fresh-expression}
([discussion](#sec-fresh-expression)) 

````grammar
FreshExpression_ =
  "fresh" [ "@" LabelName ]
  "(" Expression(allowLemma: true, allowLambda: true) ")"
````

#### 17.2.7.24. Allocated Expressions {#g-allocated-expression}
([discussion](#sec-allocated-expression)) 

````grammar
AllocatedExpression_ =
  "allocated" "(" Expression(allowLemma: true, allowLambda: true) ")"
````

#### 17.2.7.25. Unchanged Expressions {#g-unchanged-expression}
([discussion](#sec-unchanged-expression)) 

````grammar
UnchangedExpression_ =
  "unchanged" [ "@" LabelName ]
  "(" FrameExpression(allowLemma: true, allowLambda: true)
      { "," FrameExpression(allowLemma: true, allowLambda: true) }
  ")"
````

#### 17.2.7.26. Cardinality Expressions {#g-cardinality-expression}
([discussion](#sec-cardinality-expression)) 

````grammar
CardinalityExpression_ =
  "|" Expression(allowLemma: true, allowLambda: true) "|"
````

#### 17.2.7.27. Parenthesized Expression {#g-parenthesized-expression}
([discussion](#sec-parenthesized-expression)) 

````grammar
ParensExpression =
  "(" [ TupleArgs ] ")"

TupleArgs =
  [ "ghost" ]
  ActualBinding(isGhost) // argument is true iff the ghost modifier is present
  { ","
    [ "ghost" ]
    ActualBinding(isGhost) // argument is true iff the ghost modifier is present
  }
````

#### 17.2.7.28. Sequence Display Expression {#g-sequence-display-expression}
([discussion](#sec-seq-comprehension)) 

````grammar
SeqDisplayExpr =
  ( "[" [ Expressions ] "]"
  | "seq" [ GenericInstantiation ]
    "(" Expression(allowLemma: true, allowLambda: true)
    "," Expression(allowLemma: true, allowLambda: true)
    ")"
  )
````

#### 17.2.7.29. Set Display Expression {#g-set-display-expression}
([discussion](#sec-set-display-expression)) 

````grammar
SetDisplayExpr =
  ( [ "iset" | "multiset" ] "{" [ Expressions ] "}"
  | "multiset" "(" Expression(allowLemma: true,
                              allowLambda: true) ")"
  )
````

#### 17.2.7.30. Map Display Expression {#g-map-display-expression}
([discussion](#sec-map-display-expression)) 

````grammar
MapDisplayExpr =
  ("map" | "imap" ) "[" [ MapLiteralExpressions ] "]"

MapLiteralExpressions =
  Expression(allowLemma: true, allowLambda: true)
  ":=" 
  Expression(allowLemma: true, allowLambda: true)
  { "," 
    Expression(allowLemma: true, allowLambda: true)
    ":=" 
    Expression(allowLemma: true, allowLambda: true)
  }
````

#### 17.2.7.31. Endless Expression {#g-endless-expression}
([discussion](#sec-endless-expression)) 

````grammar
EndlessExpression(allowLemma, allowLambda, allowBitwiseOps) =
  ( IfExpression(allowLemma, allowLambda, allowBitwiseOps)
  | MatchExpression(allowLemma, allowLambda, allowBitwiseOps)
  | QuantifierExpression(allowLemma, allowLambda)
  | SetComprehensionExpr(allowLemma, allowLambda, allowBitwiseOps)
  | StmtInExpr
    Expression(allowLemma, allowLambda, allowBitwiseOps)
  | LetExpression(allowLemma, allowLambda, allowBitwiseOps)
  | MapComprehensionExpr(allowLemma, allowLambda, allowBitwiseOps)
  )
````

#### 17.2.7.32. If expression {#g-if-expression}
([discussion](#sec-if-expression)) 

````grammar
IfExpression(allowLemma, allowLambda, allowBitwiseOps) =
    "if" ( BindingGuard(allowLambda: true)
         | Expression(allowLemma: true, allowLambda: true, allowBitwiseOps: true)
         )
    "then" Expression(allowLemma: true, allowLambda: true, allowBitwiseOps: true)
    "else" Expression(allowLemma, allowLambda, allowBitwiseOps)
````

#### 17.2.7.33. Match Expression {#g-match-expression}
([discussion](#sec-match-expression)) 

````grammar
MatchExpression(allowLemma, allowLambda, allowBitwiseOps) =
  "match"
  Expression(allowLemma, allowLambda, allowBitwiseOps)
  ( "{" { CaseExpression(allowLemma: true, allowLambda, allowBitwiseOps: true) } "}"
  | { CaseExpression(allowLemma, allowLambda, allowBitwiseOps) }
  )

CaseExpression(allowLemma, allowLambda, allowBitwiseOps) =
  "case" { Attribute } ExtendedPattern "=>" Expression(allowLemma, allowLambda, allowBitwiseOps)
````

#### 17.2.7.34. Case and Extended Patterns {#g-pattern}
([discussion](#sec-case-pattern)) 

````grammar
CasePattern =
  ( IdentTypeOptional
  | [Ident] "(" [ CasePattern { "," CasePattern } ] ")"
  )

SingleExtendedPattern =
  ( PossiblyNegatedLiteralExpression
  | IdentTypeOptional
  | [ Ident ] "(" [ SingleExtendedPattern { "," SingleExtendedPattern } ] ")"
  )

ExtendedPattern =
  ( [ "|" ] SingleExtendedPattern { "|" SingleExtendedPattern } )

PossiblyNegatedLiteralExpression =
  ( "-" ( Nat | Dec )
  | LiteralExpression
  )
````

#### 17.2.7.35. Quantifier expression {#g-quantifier-expression}
([discussion](#sec-quantifier-expression)) 

````grammar
QuantifierExpression(allowLemma, allowLambda) =
  ( "forall" | "exists" ) QuantifierDomain "::"
  Expression(allowLemma, allowLambda)
````

#### 17.2.7.36. Set Comprehension Expressions {#g-set-comprehension-expression}
([discussion](#sec-set-comprehension-expression)) 

````grammar
SetComprehensionExpr(allowLemma, allowLambda) =
  [ "set" | "iset" ]
  QuantifierDomain(allowLemma, allowLambda)
  [ "::" Expression(allowLemma, allowLambda) ]
````

#### 17.2.7.37. Map Comprehension Expression {#g-map-comprehension-expression}
([discussion](#sec-map-comprehension-expression)) 

````grammar
MapComprehensionExpr(allowLemma, allowLambda) =
  ( "map" | "imap" )
  QuantifierDomain(allowLemma, allowLambda)
  "::"
  Expression(allowLemma, allowLambda)
  [ ":=" Expression(allowLemma, allowLambda) ]
````


#### 17.2.7.38. Statements in an Expression {#g-statement-in-expression}
([discussion](#sec-statement-in-an-expression)) 

````grammar
StmtInExpr = ( AssertStmt | AssumeStmt | ExpectStmt
             | RevealStmt | CalcStmt
             )
````

#### 17.2.7.39. Let and Let or Fail Expression {#g-let-expression}
([discussion](#sec-let-expression)) 

````grammar
LetExpression(allowLemma, allowLambda) =
  (
    [ "ghost" ] "var" CasePattern { "," CasePattern }
    ( ":=" | ":-" | { Attribute } ":|" )
    Expression(allowLemma: false, allowLambda: true)
    { "," Expression(allowLemma: false, allowLambda: true) }
  |
    ":-"
    Expression(allowLemma: false, allowLambda: true)
  )
  ";"
  Expression(allowLemma, allowLambda)
````

#### 17.2.7.40. Name Segment {#g-name-segment}
([discussion](#sec-name-segment)) 

````grammar
NameSegment = Ident [ GenericInstantiation | HashCall ]
````

#### 17.2.7.41. Hash Call {#g-hash-call}
([discussion](#sec-hash-call)) 

````grammar
HashCall = "#" [ GenericInstantiation ]
  "[" Expression(allowLemma: true, allowLambda: true) "]"
  "(" [ Bindings ] ")"
````

#### 17.2.7.42. Suffix {#g-suffix}
([discussion](#sec-suffix)) 

````grammar
Suffix =
  ( AugmentedDotSuffix_
  | DatatypeUpdateSuffix_
  | SubsequenceSuffix_
  | SlicesByLengthSuffix_
  | SequenceUpdateSuffix_
  | SelectionSuffix_
  | ArgumentListSuffix_
  )
````

#### 17.2.7.43. Augmented Dot Suffix {#g-augmented-dot-suffix}
([discussion](#sec-augmented-dot-suffix)) 

````grammar
AugmentedDotSuffix_ = "." DotSuffix
                      [ GenericInstantiation | HashCall ]
````

#### 17.2.7.44. Datatype Update Suffix {#g-datatype-update-suffix}
([discussion](#sec-datatype-update-suffix)) 

````grammar
DatatypeUpdateSuffix_ =
  "." "(" MemberBindingUpdate { "," MemberBindingUpdate } ")"

MemberBindingUpdate =
  ( ident | digits )
  ":=" Expression(allowLemma: true, allowLambda: true)
````

#### 17.2.7.45. Subsequence Suffix {#g-subsequence-suffix}
([discussion](#sec-subsequence-suffix)) 

````grammar
SubsequenceSuffix_ =
  "[" [ Expression(allowLemma: true, allowLambda: true) ]
      ".." [ Expression(allowLemma: true, allowLambda: true) ]
  "]"
````

#### 17.2.7.46. Subsequence Slices Suffix {#g-subsequence-slices-suffix}
([discussion](#sec-subsequence-slices-suffix)) 

````grammar
SlicesByLengthSuffix_ =
  "[" Expression(allowLemma: true, allowLambda: true) ":"
      [
        Expression(allowLemma: true, allowLambda: true)
        { ":" Expression(allowLemma: true, allowLambda: true) }
        [ ":" ]
      ]
  "]"
````

#### 17.2.7.47. Sequence Update Suffix {#g-sequence-update-suffix}
([discussion](#sec-sequence-update-suffix)) 

````grammar
SequenceUpdateSuffix_ =
  "[" Expression(allowLemma: true, allowLambda: true)
      ":=" Expression(allowLemma: true, allowLambda: true)
  "]"
````

#### 17.2.7.48. Selection Suffix {#g-selection-suffix}
([discussion](#sec-selection-suffix)) 

````grammar
SelectionSuffix_ =
  "[" Expression(allowLemma: true, allowLambda: true)
      { "," Expression(allowLemma: true, allowLambda: true) }
  "]"
````

#### 17.2.7.49. Argument List Suffix {#g-argument-list-suffix}
([discussion](#sec-argument-list-suffix)) 

````grammar
ArgumentListSuffix_ = "(" [ Expressions ] ")"
````

#### 17.2.7.50. Expression Lists {#g-expression-list}
([discussion](#sec-expression-list)) 

````grammar
Expressions =
  Expression(allowLemma: true, allowLambda: true)
  { "," Expression(allowLemma: true, allowLambda: true) }
````

#### 17.2.7.51. Parameter Bindings {#g-parameter-bindings}
([discussion](#sec-parameter-bindings)) 

````grammar
ActualBindings =
  ActualBinding
  { "," ActualBinding }

ActualBinding(isGhost = false) =
  [ NoUSIdentOrDigits ":=" ]
  Expression(allowLemma: true, allowLambda: true)
````

#### 17.2.7.52. Quantifier domains {#g-quantifier-domain}

````grammar
QuantifierDomain(allowLemma, allowLambda) =
  QuantifierVarDecl(allowLemma, allowLambda) 
  { "," QuantifierVarDecl(allowLemma, allowLambda) }

QuantifierVarDecl(allowLemma, allowLambda) =
  IdentTypeOptional
  [ "<-" Expression(allowLemma, allowLambda) ]
  { Attribute }
  [ | Expression(allowLemma, allowLambda) ]
````


#### 17.2.7.53. Basic name and type combinations

````grammar
Ident = ident

DotSuffix = ( ident | digits | "requires" | "reads" )

NoUSIdent = ident - "_" { idchar }

WildIdent = NoUSIdent | "_"

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

ModuleQualifiedName = ModuleName { "." ModuleName }

IdentType = WildIdent ":" Type

FIdentType = NoUSIdentOrDigits ":" Type

CIdentType = NoUSIdentOrDigits [ ":" Type ]

GIdentType(allowGhostKeyword, allowNewKeyword, allowOlderKeyword, allowNameOnlyKeyword, allowDefault) =
  { "ghost" | "new" | "nameonly" | "older" } IdentType
  [ ":=" Expression(allowLemma: true, allowLambda: true) ]

LocalIdentTypeOptional = WildIdent [ ":" Type ]

IdentTypeOptional = WildIdent [ ":" Type ]

TypeIdentOptional =
  { "ghost" | "nameonly" } [ NoUSIdentOrDigits ":" ] Type
  [ ":=" Expression(allowLemma: true, allowLambda: true) ]

FormalsOptionalIds = "(" [ TypeIdentOptional
                           { "," TypeIdentOptional } ] ")"

````
