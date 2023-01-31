# 29. Dafny Grammar {#sec-grammar-details}

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




## 29.1. Dafny Syntax

This section gives the definitions of Dafny tokens.

### 29.1.1. Classes of characters

These definitions define some names as representing subsets of the set of characters. Here

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

### 29.1.2. Definitions of tokens {#sec-g-tokens}

These definitions use 

* double-quotes to indicate a verbatim string (with no escaping of characters)
* `'"'` to indicate a literal double-quote character
* vertical bar to indicate alternatives
* square brackets to indicate an optional part
* curly braces to indicate 0-or-more repetitions
* parentheses to indicate grouping
* a `-` sign to indicate set difference: any character sequence matched by the left operand except character sequences matched by the right operand
* a sequence of any of the above indicates concatentation (without whitespace)

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

* `least` and `greatest` are recognized as adjectives to the keyword `predicate` (cf. [Section 24.4](#sec-extreme)).
* `older` is a modifier for parameters of non-extreme predicates (cf. [Section 12.4.6](#sec-older-parameters)).

The `\uXXXX` form of an `escapedChar` is only used when the option `--unicode-char=false` is set (which is the default for Dafny 3.x);
the `\U{XXXXXX}` form of an `escapedChar` is only used when the option `--unicode-char=true` is set (which is the default for Dafny 4.x).

## 29.2. Dafny Grammar productions

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

### 29.2.1. Programs ([discussion](#sec-program)) {#g-program}

````grammar
Dafny = { IncludeDirective_ } { TopDecl(isTopLevel:true, isAbstract: false) } EOF
````

#### 29.2.1.1. Include directives ([discussion](#sec-include-directive)) {#g-include-directive}

````grammar
IncludeDirective_ = "include" stringToken
````

#### 29.2.1.2. Top-level declarations ([discussion](#sec-top-level-declaration)) {#g-top-level-declaration}

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
  | ClassMemberDecl(moduleLevelDecl: true)
  )
````

#### 29.2.1.3. Declaration modifiers ([discussion](#sec-declaration-modifier)) {#g-declaration-modifier}

````grammar
DeclModifier = ( "abstract" | "ghost" | "static" )
````

### 29.2.2. Modules {#g-module}

````grammar
SubModuleDecl(isTopLevel) = ( ModuleDefinition | ModuleImport | ModuleExport )
````

Module export declarations are not permitted if isTopLevel is true.

#### 29.2.2.1. Module Definitions ([discussion](#sec-module-definition)) {#g-module-definition}

````grammar
ModuleDefinition = 
  "module" { Attribute } ModuleQualifiedName
  [ "refines" ModuleQualifiedName ]
  "{" { TopDecl(isTopLevel:false, isAbstract) } "}"
````

The `isAbstract` argument is true i the DeclModifiers include "abstract".

#### 29.2.2.2. Module Imports ([discussion](#sec-importing-modules)) {#g-module-import}

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

#### 29.2.2.3. Module Export Definitions ([discussion](#sec-export-sets)) {#g-module-export}

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

### 29.2.3. Types ([discussion](#sec-types)) {#g-type}

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


#### 29.2.3.1. Basic types ([discussion](#sec-basic-type)) {#g-basic-type}
````grammar
BoolType_ = "bool"
IntType_ = "int"
RealType_ = "real"
BitVectorType_ = bvToken
OrdinalType_ = "ORDINAL"
CharType_ = "char"
````


#### 29.2.3.2. Generic instantiation ([discussion](#sec-generic-instantiation)) {#g-generic-instantiation}

````grammar
GenericInstantiation = "<" Type { "," Type } ">"
````

#### 29.2.3.3. Type parameter ([discussion](#sec-type-parameters)) {#g-type-parameter}

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

#### 29.2.3.4. Collection types ([discussion](#sec-collection-types)) {#g-collection-type}
````grammar
FiniteSetType_ = "set" [ GenericInstantiation ]

InfiniteSetType_ = "iset" [ GenericInstantiation ]

MultisetType_ = "multiset" [ GenericInstantiation ]

SequenceType_ = "seq" [ GenericInstantiation ]

StringType_ = "string"

FiniteMapType_ = "map" [ GenericInstantiation ]

InfiniteMapType_ = "imap" [ GenericInstantiation ]
````

#### 29.2.3.5. Type definitions ([discussion](#sec-type-definition)) {#g-type-definition}

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


#### 29.2.3.6. Class type ([discussion](#sec-class-types)) {#g-class-type}

````grammar
ClassDecl = "class" { Attribute } ClassName [ GenericParameters ]
  ["extends" Type {"," Type} | ellipsis ]
  "{" { { DeclModifier }
        ClassMemberDecl(allowConstructors: true,
                        isValueType: false,
                        moduleLevelDecl: false,
                        isWithinAbstractModule: false) }
  "}"

ClassMemberDecl(allowConstructors, isValueType,
                moduleLevelDecl, isWithinAbstractModule) =
  ( FieldDecl(isValueType) // allowed iff moduleLevelDecl is false
  | ConstantFieldDecl(moduleLevelDecl)
  | FunctionDecl(isWithinAbstractModule)
  | MethodDecl(isGhost: "ghost" was present,
               allowConstructors, isWithinAbstractModule)
  )
````


#### 29.2.3.7. Trait types ([discussion](#sec-trait-types)) {#g-trait-type}

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

#### 29.2.3.8. Object type ([discussion](#sec-object-type)) {#g-object-type}

````grammar
ObjectType_ = "object" | "object?"
````

#### 29.2.3.9. Array types ([discussion](#sec-array-type)) {#g-array-type}

````grammar
ArrayType_ = arrayToken [ GenericInstantiation ]
````

#### 29.2.3.10. Iterator types ([discussion](#sec-iterator-types)) {#g-iterator-type}

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

#### 29.2.3.11. Arrow types ([discussion](#sec-arrow-types)) {#g-arrow-type}

````grammar
ArrowType_ = ( DomainType_ "~>" Type
             | DomainType_ "-->" Type
             | DomainType_ "->" Type
             )
````

#### 29.2.3.12. Algebraic datatypes ([discussion](#sec-datatype)) {#g-datatype}

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

### 29.2.4. Type member declarations ([discussion](#sec-member-declaration)) {#g-member-declaration}

#### 29.2.4.1. Fields ([discussion](#sec-field-declaration)) {#g-field-declaration}

````grammar
FieldDecl(isValueType) =
  "var" { Attribute } FIdentType { "," FIdentType }
````
A `FieldDecl` is not permitted if `isValueType` is true.

#### 29.2.4.2. Constant fields ([discussion](#sec-constant-field-declaration)) {#g-const-declaration}

````grammar
ConstantFieldDecl(moduleLevelDecl) =
  "const" { Attribute } CIdentType [ ellipsis ]
   [ ":=" Expression(allowLemma: false, allowLambda:true) ]
````

If `moduleLevelDecl` is true, then the `static` modifier is not permitted
(the constant field is static implicitly).

#### 29.2.4.3. Method declarations ([discussion](#sec-method-declaration)) {#g-method-declaration}

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

#### 29.2.4.4. Function declarations ([discussion](#sec-function-declaration)) {#g-function-declaration}


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

### 29.2.5. Specifications

#### 29.2.5.1. Method specifications ([discussion](#sec-method-specification)) {#g-method-specification}

````grammar
MethodSpec =
  { ModifiesClause(allowLambda: false)
  | RequiresClause(allowLabel: true)
  | EnsuresClause(allowLambda: false)
  | DecreasesClause(allowWildcard: true, allowLambda: false)
  }
````

#### 29.2.5.2. Function specifications ([discussion](#sec-function-specification)) {#g-function-specification}

````grammar
FunctionSpec =
  { RequiresClause(allowLabel: true)
  | ReadsClause(allowLemma: false, allowLambda: false, allowWild: true)
  | EnsuresClause(allowLambda: false)
  | DecreasesClause(allowWildcard: false, allowLambda: false)
  }
````

#### 29.2.5.3. Lambda function specifications ([discussion](#sec-lambda-specification)) {#g-lambda-specification}

````grammar
LambdaSpec =
  { ReadsClause(allowLemma: true, allowLambda: false, allowWild: true)
  | "requires" Expression(allowLemma: false, allowLambda: false)
  }
````

#### 29.2.5.4. Iterator specifications ([discussion](#sec-iterator-specification)) {#g-iterator-specification}

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

#### 29.2.5.5. Loop specifications ([discussion](#sec-loop-specification)) {#g-loop-specification}

````grammar
LoopSpec =
  { InvariantClause_
  | DecreasesClause(allowWildcard: true, allowLambda: true)
  | ModifiesClause(allowLambda: true)
  }
````



#### 29.2.5.6. Requires clauses ([discussion](#sec-requires-clause)) {#g-requires-clause}

````grammar
RequiresClause(allowLabel) =
  "requires" { Attribute }
  [ LabelName ":" ]  // Label allowed only if allowLabel is true
  Expression(allowLemma: false, allowLambda: false)
````

#### 29.2.5.7. Ensures clauses ([discussion](#sec-ensures-clause)) {#g-ensures-clause}

````grammar
EnsuresClause(allowLambda) =
  "ensures" { Attribute } Expression(allowLemma: false, allowLambda)
````

#### 29.2.5.8. Decreases clauses ([discussion](#sec-decreases-clause)) {#g-decreases-clause}

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

#### 29.2.5.9. Modifies clauses ([discussion](#sec-modifies-clause)) {#g-modifies-clause}

````grammar
ModifiesClause(allowLambda) =
  "modifies" { Attribute }
  FrameExpression(allowLemma: false, allowLambda)
  { "," FrameExpression(allowLemma: false, allowLambda) }
````

#### 29.2.5.10. Invariant clauses ([discussion](#sec-invariant-clause)) {#g-invariant-clause}

````grammar
InvariantClause_ =
  "invariant" { Attribute }
  Expression(allowLemma: false, allowLambda: true)
````

#### 29.2.5.11. Reads clauses ([discussion](#sec-reads-clause)) {#g-reads-clause}

````grammar
ReadsClause(allowLemma, allowLambda, allowWild) =
  "reads"
  { Attribute }
  PossiblyWildFrameExpression(allowLemma, allowLambda, allowWild)
  { "," PossiblyWildFrameExpression(allowLemma, allowLambda, allowWild) }
````

#### 29.2.5.12. Frame expressions ([discussion](#sec-frame-expression)) {#g-frame-expression}

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






### 29.2.6. Statements {#g-statement}

#### 29.2.6.1. Labeled statement ([discussion](#sec-labeled-statement)) {#g-labeled-statement}

````grammar
Stmt = { "label" LabelName ":" } NonLabeledStmt
````

#### 29.2.6.2. Non-Labeled statement ([discussion](#sec-nonlabeled-statement)) {#g-nonlabeled-statement}

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

#### 29.2.6.3. Break and continue statements ([discussion](#sec-break-continue-statement)) {#g-break-continue-statement}

````grammar
BreakStmt =
  ( "break" LabelName ";"
  | "continue" LabelName ";"
  | { "break" } "break" ";"
  | { "break" } "continue" ";"
  )
````

#### 29.2.6.4. Block statement ([discussion](#sec-block-statement)) {#g-block-statement}

````grammar
BlockStmt = "{" { Stmt } "}"
````

#### 29.2.6.5. Return statement ([discussion](#sec-return-statement)) {#g-return-statement}

````grammar
ReturnStmt = "return" [ Rhs { "," Rhs } ] ";"
````

#### 29.2.6.6. Yield statement ([discussion](#sec-yield-statement)) {#g-yield-statement}

````grammar
YieldStmt = "yield" [ Rhs { "," Rhs } ] ";"
````

#### 29.2.6.7. Update and call statement ([discussion](#sec-update-and-call-statement)) {#g-update-and-call-statement}

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

#### 29.2.6.8. Update with failure statement ([discussion](#sec-update-with-failure-statement)) {#g-update-with-failure-statement}

````grammar
UpdateFailureStmt  =
  [ Lhs { "," Lhs } ]
  ":-"
  [ "expect"  | "assert" | "assume" ]
  Expression(allowLemma: false, allowLambda: false)
  { "," Rhs }
  ";"
````

#### 29.2.6.9. Variable declaration statement ([discussion](#sec-variable-declaration-statement)) {#g-variable-declaration-statement}

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

#### 29.2.6.10. Guards ([discussion](#sec-guard)) {#g-guard}

````grammar
Guard = ( "*"
        | "(" "*" ")"
        | Expression(allowLemma: true, allowLambda: true)
        )
````

#### 29.2.6.11. Binding guards ([discussion](#sec-binding-guards)) {#g-binding-guard} 

````grammar
BindingGuard(allowLambda) =
  IdentTypeOptional { "," IdentTypeOptional }
  { Attribute }
  ":|"
  Expression(allowLemma: true, allowLambda)
````

#### 29.2.6.12. If statement ([discussion](#sec-if-statement)) {#g-if-statement}

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

#### 29.2.6.13. While Statement ([discussion](#sec-while-statement)) {#g-while-statement}

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

#### 29.2.6.14. For statement ([discussion](#sec-for-statement)) {#g-for-statement}

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

#### 29.2.6.15. Match statement ([discussion](#sec-match-statement)) {#g-match-statement}

````grammar
MatchStmt =
  "match"
  Expression(allowLemma: true, allowLambda: true)
  ( "{" { CaseStmt } "}"
  | { CaseStmt }
  )

CaseStmt = "case" ExtendedPattern "=>" { Stmt }
````

#### 29.2.6.16. Assert statement ([discussion](#sec-assert-statement)) {#g-assert-statement}

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

#### 29.2.6.17. Assume statement ([discussion](#sec-assume-statement)) {#g-assume-statement}

````grammar
AssumeStmt =
  "assume"
  { Attribute }
  Expression(allowLemma: false, allowLambda: true)
  ";"
````

#### 29.2.6.18. Expect statement ([discussion](#sec-expect-statement)) {#g-expect-statement}

````grammar
ExpectStmt =
  "expect"
  { Attribute }
  Expression(allowLemma: false, allowLambda: true)
  [ "," Expression(allowLemma: false, allowLambda: true) ]
  ";"
````

#### 29.2.6.19. Print statement ([discussion](#sec-print-statement)) {#g-print-statement}

````grammar
PrintStmt =
  "print"
  Expression(allowLemma: false, allowLambda: true)
  { "," Expression(allowLemma: false, allowLambda: true) }
  ";"
````

#### 29.2.6.20. Reveal statement ([discussion](#sec-reveal-statement)) {#g-reveal-statement}

````grammar
RevealStmt =
  "reveal"
  Expression(allowLemma: false, allowLambda: true)
  { "," Expression(allowLemma: false, allowLambda: true) }
  ";"
````
#### 29.2.6.21. Forall statement ([discussion](#sec-forall-statement)) {#g-forall-statement}

````grammar
ForallStmt =
  "forall"
  ( "(" [ QuantifierDomain ] ")"
  | [ QuantifierDomain ]
  )
  { EnsuresClause(allowLambda: true) }
  [ BlockStmt ]
````
#### 29.2.6.22. Modify statement ([discussion](#sec-modify-statement)) {#g-modify-statement}

````grammar
ModifyStmt =
  "modify"
  { Attribute }
  FrameExpression(allowLemma: false, allowLambda: true)
  { "," FrameExpression(allowLemma: false, allowLambda: true) }
  ";"
````

#### 29.2.6.23. Calc statement ([discussion](#sec-calc-statement)) {#g-calc-statement}

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

### 29.2.7. Expressions

#### 29.2.7.1. Top-level expression ([discussion](#sec-top-level-expression)) {#g-top-level-expression}

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

#### 29.2.7.2. Equivalence expression ([discussion](#sec-equivalence-expression)) {#g-equivalence-expression}

````grammar
EquivExpression(allowLemma, allowLambda, allowBitwiseOps) =
  ImpliesExpliesExpression(allowLemma, allowLambda, allowBitwiseOps)
  { "<==>" ImpliesExpliesExpression(allowLemma, allowLambda, allowBitwiseOps) }
````

#### 29.2.7.3. Implies expression ([discussion](#sec-implies-expression)) {#g-implies-expression}

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

#### 29.2.7.4. Logical expression ([discussion](#sec-logical-expression)) {#g-logical-expression}

````grammar
LogicalExpression(allowLemma, allowLambda, allowBitwiseOps) =
  [ "&&" | "||" ]
  RelationalExpression(allowLemma, allowLambda, allowBitwiseOps)
  { ( "&&" | "||" )
    RelationalExpression(allowLemma, allowLambda, allowBitwiseOps)
  }
````

#### 29.2.7.5. Relational expression ([discussion](#sec-relational-expression)) {#g-relational-expression}

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

#### 29.2.7.6. Bit-shift expression ([discussion](#sec-bit-shift-expression)) {#g-bit-shift-expression}

````grammar
ShiftTerm(allowLemma, allowLambda, allowBitwiseOps) =
  Term(allowLemma, allowLambda, allowBitwiseOps)
  { ShiftOp Term(allowLemma, allowLambda, allowBitwiseOps) }

ShiftOp = ( "<<" | ">>" )
````

#### 29.2.7.7. Term (addition operations) ([discussion](#sec-addition-expression)) {#g-term}

````grammar
Term(allowLemma, allowLambda, allowBitwiseOps) =
  Factor(allowLemma, allowLambda, allowBitwiseOps)
  { AddOp Factor(allowLemma, allowLambda, allowBitwiseOps) }

AddOp = ( "+" | "-" )
````

#### 29.2.7.8. Factor (multiplication operations) ([discussion](#sec-multiplication-expression)) {#g-factor}

````grammar
Factor(allowLemma, allowLambda, allowBitwiseOps) =
  BitvectorFactor(allowLemma, allowLambda, allowBitwiseOps)
  { MulOp BitvectorFactor(allowLemma, allowLambda, allowBitwiseOps) }

MulOp = ( "*" | "/" | "%" )
````

#### 29.2.7.9. Bit-vector expression ([discussion](#sec-bitvector-expression)) {#g-bit-vector-expression}

````grammar
BitvectorFactor(allowLemma, allowLambda, allowBitwiseOps) =
  AsExpression(allowLemma, allowLambda, allowBitwiseOps)
  { BVOp AsExpression(allowLemma, allowLambda, allowBitwiseOps) }

BVOp = ( "|" | "&" | "^" )
````

If `allowBitwiseOps` is false, it is an error to have a bitvector operation.

#### 29.2.7.10. As/Is expression ([discussion](#sec-as-is-expression)) {#g-as-is-expression}

````grammar
AsExpression(allowLemma, allowLambda, allowBitwiseOps) =
  UnaryExpression(allowLemma, allowLambda, allowBitwiseOps)
  { ( "as" | "is" ) Type }
````

#### 29.2.7.11. Unary expression ([discussion](#sec-unary-expression)) {#g-unary-expression}
````grammar
UnaryExpression(allowLemma, allowLambda, allowBitwiseOps) =
  ( "-" UnaryExpression(allowLemma, allowLambda, allowBitwiseOps)
  | "!" UnaryExpression(allowLemma, allowLambda, allowBitwiseOps)
  | PrimaryExpression(allowLemma, allowLambda, allowBitwiseOps)
  )
````

#### 29.2.7.12. Primary expression ([discussion](#sec-primary-expression)) {#g-primary-expression}
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

#### 29.2.7.13. Lambda expression ([discussion](#sec-lambda-expression)) {#g-lambda-expression}
````grammar
LambdaExpression(allowLemma, allowBitwiseOps) =
  ( WildIdent
  | "(" [ IdentTypeOptional { "," IdentTypeOptional } ] ")"
  )
  LambdaSpec
  "=>"
  Expression(allowLemma, allowLambda: true, allowBitwiseOps)
````

#### 29.2.7.14. Left-hand-side expression ([discussion](#sec-lhs-expression)) {#g-lhs-expression}
````grammar
Lhs =
  ( NameSegment { Suffix }
  | ConstAtomExpression Suffix { Suffix }
  )
````

#### 29.2.7.15. Right-hand-side expression ([discussion](#sec-rhs-expression)) {#g-rhs-expression}
<pre>
Rhs =
  ( <a href="#g-array-allocation-expression">ArrayAllocation_</a>
  | <a href="#g-object-allocation-expression">ObjectAllocation_</a>
  | Expression(allowLemma: false, allowLambda: true, allowBitwiseOps: true)
  | <a href="#g-havoc-expression">HavocRhs_</a>
  )
  { Attribute }
</pre>

#### 29.2.7.16. Array allocation right-hand-side expression ([discussion](#sec-array-allocation)) {#g-array-allocation-expression}
````grammar
ArrayAllocation_ =
  "new" [ Type ] "[" [ Expressions ] "]"
  [ "(" Expression(allowLemma: true, allowLambda: true) ")"
  | "[" [ Expressions ] "]"
  ]
````

#### 29.2.7.17. Object allocation right-hand-side expression ([discussion](#sec-object-allocation)) {#g-object-allocation-expression}
````grammar
ObjectAllocation_ = "new" Type [ "." TypeNameOrCtorSuffix ]
                               [ "(" [ Bindings ] ")" ]
````

#### 29.2.7.18. Havoc right-hand-side expression ([discussion](#sec-havoc-expression)) {#g-havoc-expression}
````grammar
HavocRhs_ = "*"
````

#### 29.2.7.19. Atomic expressions ([discussion](#sec-atomic-expression)) {#g-atomic-expression}

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

#### 29.2.7.20. Literal expressions ([discussion](#sec-literal-expression)) {#g-literal-expression}

````grammar
LiteralExpression =
 ( "false" | "true" | "null" | Nat | Dec |
   charToken | stringToken )

Nat = ( digits | hexdigits )

Dec = decimaldigits
````

#### 29.2.7.21. This expression ([discussion](#sec-this-expression)) {#g-this-expression}

````grammar
ThisExpression_ = "this"
````

#### 29.2.7.22. Old and Old@ Expressions ([discussion](#sec-old-expression)) {#g-old-expression}

````grammar
OldExpression_ =
  "old" [ "@" LabelName ]
  "(" Expression(allowLemma: true, allowLambda: true) ")"
````

#### 29.2.7.23. Fresh Expressions ([discussion](#sec-fresh-expression)) {#g-fresh-expression}

````grammar
FreshExpression_ =
  "fresh" [ "@" LabelName ]
  "(" Expression(allowLemma: true, allowLambda: true) ")"
````

#### 29.2.7.24. Allocated Expressions ([discussion](#sec-allocated-expression)) {#g-allocated-expression}

````grammar
AllocatedExpression_ =
  "allocated" "(" Expression(allowLemma: true, allowLambda: true) ")"
````

#### 29.2.7.25. Unchanged Expressions ([discussion](#sec-unchanged-expression)) {#g-unchanged-expression}

````grammar
UnchangedExpression_ =
  "unchanged" [ "@" LabelName ]
  "(" FrameExpression(allowLemma: true, allowLambda: true)
      { "," FrameExpression(allowLemma: true, allowLambda: true) }
  ")"
````

#### 29.2.7.26. Cardinality Expressions ([discussion](#sec-cardinality-expression)) {#g-cardinality-expression}

````grammar
CardinalityExpression_ =
  "|" Expression(allowLemma: true, allowLambda: true) "|"
````

#### 29.2.7.27. Parenthesized Expression ([discussion](#sec-parenthesized-expression)) {#g-parenthesized-expression}

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

#### 29.2.7.28. Sequence Display Expression ([discussion](#sec-seq-comprehension)) {#g-sequence-display-expression}

````grammar
SeqDisplayExpr =
  ( "[" [ Expressions ] "]"
  | "seq" [ GenericInstantiation ]
    "(" Expression(allowLemma: true, allowLambda: true)
    "," Expression(allowLemma: true, allowLambda: true)
    ")"
  )
````

#### 29.2.7.29. Set Display Expression ([discussion](#sec-set-display-expression)) {#g-set-display-expression}

````grammar
SetDisplayExpr =
  ( [ "iset" | "multiset" ] "{" [ Expressions ] "}"
  | "multiset" "(" Expression(allowLemma: true,
                              allowLambda: true) ")"
  )
````

#### 29.2.7.30. Map Display Expression ([discussion](#sec-map-display-expression)) {#g-map-display-expression}

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

#### 29.2.7.31. Endless Expression ([discussion](#sec-endless-expression)) {#g-endless-expression}

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

#### 29.2.7.32. If expression ([discussion](#sec-if-expression)) {#g-if-expression}

````grammar
IfExpression(allowLemma, allowLambda, allowBitwiseOps) =
    "if" ( BindingGuard(allowLambda: true)
         | Expression(allowLemma: true, allowLambda: true, allowBitwiseOps: true)
         )
    "then" Expression(allowLemma: true, allowLambda: true, allowBitwiseOps: true)
    "else" Expression(allowLemma, allowLambda, allowBitwiseOps)
````

#### 29.2.7.33. Match Expression ([discussion](#sec-match-expression)) {#g-match-expression}

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

#### 29.2.7.34. Case and Extended Patterns ([discussion](#sec-case-pattern)) {#g-pattern}

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

#### 29.2.7.35. Quantifier expression ([discussion](#sec-quantifier-expression)) {#g-quantifier-expression}

````grammar
QuantifierExpression(allowLemma, allowLambda) =
  ( "forall" | "exists" ) QuantifierDomain "::"
  Expression(allowLemma, allowLambda)
````

#### 29.2.7.36. Set Comprehension Expressions ([discussion](#sec-set-comprehension-expression)) {#g-set-comprehension-expression}

````grammar
SetComprehensionExpr(allowLemma, allowLambda) =
  [ "set" | "iset" ]
  QuantifierDomain(allowLemma, allowLambda)
  [ "::" Expression(allowLemma, allowLambda) ]
````

#### 29.2.7.37. Map Comprehension Expression ([discussion](#sec-map-comprehension-expression)) {#g-map-comprehension-expression}

````grammar
MapComprehensionExpr(allowLemma, allowLambda) =
  ( "map" | "imap" )
  QuantifierDomain(allowLemma, allowLambda)
  "::"
  Expression(allowLemma, allowLambda)
  [ ":=" Expression(allowLemma, allowLambda) ]
````


#### 29.2.7.38. Statements in an Expression ([discussion](#sec-statement-in-an-expression)) {#g-statement-in-expression}

````grammar
StmtInExpr = ( AssertStmt | AssumeStmt | ExpectStmt
             | RevealStmt | CalcStmt
             )
````

#### 29.2.7.39. Let and Let or Fail Expression ([discussion](#sec-let-expression)) {#g-let-expression}

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

#### 29.2.7.40. Name Segment ([discussion](#sec-name-segment)) {#g-name-segment}

````grammar
NameSegment = Ident [ GenericInstantiation | HashCall ]
````

#### 29.2.7.41. Hash Call ([discussion](#sec-hash-call)) {#g-hash-call}

````grammar
HashCall = "#" [ GenericInstantiation ]
  "[" Expression(allowLemma: true, allowLambda: true) "]"
  "(" [ Bindings ] ")"
````

#### 29.2.7.42. Suffix ([discussion](#sec-suffix)) {#g-suffix}

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

#### 29.2.7.43. Augmented Dot Suffix ([discussion](#sec-augmented-dot-suffix))  {#g-augmented-dot-suffix}

````grammar
AugmentedDotSuffix_ = "." DotSuffix
                      [ GenericInstantiation | HashCall ]
````

#### 29.2.7.44. Datatype Update Suffix ([discussion](#sec-datatype-update-suffix))  {#g-datatype-update-suffix}

````grammar
DatatypeUpdateSuffix_ =
  "." "(" MemberBindingUpdate { "," MemberBindingUpdate } ")"

MemberBindingUpdate =
  ( ident | digits )
  ":=" Expression(allowLemma: true, allowLambda: true)
````

#### 29.2.7.45. Subsequence Suffix ([discussion](#sec-subsequence-suffix))  {#g-subsequence-suffix}

````grammar
SubsequenceSuffix_ =
  "[" [ Expression(allowLemma: true, allowLambda: true) ]
      ".." [ Expression(allowLemma: true, allowLambda: true) ]
  "]"
````

#### 29.2.7.46. Subsequence Slices Suffix ([discussion](#sec-subsequence-slices-suffix)) {#g-subsequence-slices-suffix}

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

#### 29.2.7.47. Sequence Update Suffix ([discussion](#sec-sequence-update-suffix)) {#g-sequence-update-suffix}

````grammar
SequenceUpdateSuffix_ =
  "[" Expression(allowLemma: true, allowLambda: true)
      ":=" Expression(allowLemma: true, allowLambda: true)
  "]"
````

#### 29.2.7.48. Selection Suffix ([discussion](#sec-selection-suffix)) {#g-selection-suffix}

````grammar
SelectionSuffix_ =
  "[" Expression(allowLemma: true, allowLambda: true)
      { "," Expression(allowLemma: true, allowLambda: true) }
  "]"
````

#### 29.2.7.49. Argument List Suffix ([discussion](#sec-argument-list-suffix)) {#g-argument-list-suffix}

````grammar
ArgumentListSuffix_ = "(" [ Expressions ] ")"
````

#### 29.2.7.50. Expression Lists ([discussion](#sec-expression-list)) {#g-expression-list}

````grammar
Expressions =
  Expression(allowLemma: true, allowLambda: true)
  { "," Expression(allowLemma: true, allowLambda: true) }
````

#### 29.2.7.51. Parameter Bindings ([discussion](#sec-parameter-bindings)) {#g-parameter-bindings}

````grammar
ActualBindings =
  ActualBinding
  { "," ActualBinding }

ActualBinding(isGhost = false) =
  [ NoUSIdentOrDigits ":=" ]
  Expression(allowLemma: true, allowLambda: true)
````

#### 29.2.7.52. Quantifier domains {#g-quantifier-domain}

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


#### 29.2.7.53. Basic name and type combinations

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
