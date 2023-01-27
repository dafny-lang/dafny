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

These definitions define some names as representing subsets of the set of characters.
Here double quotes enclose the set of characters constituting the class, single quotes 
enclose a single character (perhaps an escaped representation using `\`), the 
binary `+` indicates set union, 
binary `-` indicates set difference, and `ANY` indicates the set of all (unicode) characters.

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
- double-quotes to indicate a verbatim string (with no escaping of characters)
- `'"'` to indicate a literal double-quote character
- vertical bar to indicate alternatives
- square brackets to indicate an optional part
- curly braces to indicate 0-or-more repetitions
- parentheses to indicate grouping
- a `-` sign to indicate set difference: any character sequence matched by the left operand except character sequences matched by the right operand
- ANY to indicate any (unicode) character
- a sequence of any of the above indicates concatentation (without whitespace)

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
* `least` and `greatest` are recognized as adjectives to the keyword `predicate` (cf. [Section 0.0.0](#sec-extreme)).
* `older` is a modifier for parameters of non-extreme predicates (cf. [Section 0.0.0](#sec-older-parameters)).

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

### 29.2.1. Programs {#g-program}

````grammar
Dafny = { IncludeDirective_ } { TopDecl } EOF
````

#### 29.2.1.1. Include directives {#g-include-directive}

````grammar
IncludeDirective_ = "include" stringToken
````

#### 29.2.1.2. Top-level declarations {#g-top-level-declaration}

````grammar
TopDecl =
  { DeclModifier }
  ( SubModuleDecl
  | ClassDecl
  | DatatypeDecl
  | NewtypeDecl
  | SynonymTypeDecl  // includes opaque types
  | IteratorDecl
  | TraitDecl
  | ClassMemberDecl(moduleLevelDecl: true)
  )
````

#### 29.2.1.3. Declaration modifiers {#g-declaration-modifiers}

````grammar
DeclModifier = ( "abstract" | "ghost" | "static" )
````

### 29.2.2. Modules {#g-module}

````grammar
SubModuleDecl = ( ModuleDefinition | ModuleImport | ModuleExport )
````

#### 29.2.2.1. Module Definitions {#g-module-definition}

````grammar
ModuleDefinition = 
  "module" { Attribute } ModuleQualifiedName
  [ "refines" ModuleQualifiedName ]
  "{" { TopDecl } "}"
````

#### 29.2.2.2. Module Imports {#g-module-import}

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

#### 29.2.2.3. Module Export Definitions {#g-module-export}

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

### 29.2.3. Types {#g-type}

#### 29.2.3.1. Basic types {#g-basic-type}

#### 29.2.3.2. Generic types {#g-generic-type}

#### 29.2.3.3. Type parameter {#g-type-parameter}

#### 29.2.3.4. Collection types {#g-collection-type}


#### 29.2.3.5. Type definitions {#g-type-definition}

#### 29.2.3.6. Classe type {#g-class-type}

#### 29.2.3.7. Traits {#g-trait} 

#### 29.2.3.8. Iterator types {#g-iterator-type}

#### 29.2.3.9. Arrow types {#g-arrow-type}

#### 29.2.3.10. Tuples type {#g-tuple-type}

#### 29.2.3.11. Datatypes {#g-datatype}

### 29.2.4. Method, Functions, and Constructors {#g-executable}


### 29.2.5. Specifications

#### 29.2.5.1. Method specifications {#g-method-specification}

````grammar
MethodSpec =
  { ModifiesClause(allowLambda: false)
  | RequiresClause(allowLabel: true)
  | EnsuresClause(allowLambda: false)
  | DecreasesClause(allowWildcard: true, allowLambda: false)
  }
````

#### 29.2.5.2. Function specifications {#g-function-specification}

````grammar
FunctionSpec =
  { RequiresClause(allowLabel: true)
  | ReadsClause(allowLemma: false, allowLambda: false, allowWild: true)
  | EnsuresClause(allowLambda: false)
  | DecreasesClause(allowWildcard: false, allowLambda: false)
  }
````

#### 29.2.5.3. Lambda function specifications {#g-lambda-specification}

````grammar
LambdaSpec =
  { ReadsClause(allowLemma: true, allowLambda: false, allowWild: true)
  | "requires" Expression(allowLemma: false, allowLambda: false)
  }
````

#### 29.2.5.4. Iterator specifications {#g-iterator-specification}

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

#### 29.2.5.5. Loop specifications {#g-loop-specification}

````grammar
LoopSpec =
  { InvariantClause_
  | DecreasesClause(allowWildcard: true, allowLambda: true)
  | ModifiesClause(allowLambda: true)
  }
````



#### 29.2.5.6. Requires clauses {#g-requires-clause}

````grammar
RequiresClause(allowLabel) =
  "requires" { Attribute }
  [ LabelName ":" ]  // Label allowed only if allowLabel is true
  Expression(allowLemma: false, allowLambda: false)
````

#### 29.2.5.7. Ensures clauses {#g-ensures-clause}

````grammar
EnsuresClause(allowLambda) =
  "ensures" { Attribute } Expression(allowLemma: false, allowLambda)
````

#### 29.2.5.8. Decreases clauses {#g-decreases-clause}

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

#### 29.2.5.10. Modifies clauses {#g-modifies-clause}

````grammar
ModifiesClause(allowLambda) =
  "modifies" { Attribute }
  FrameExpression(allowLemma: false, allowLambda)
  { "," FrameExpression(allowLemma: false, allowLambda) }
````

#### 29.2.5.11. Invariant clauses {#g-invariant-clause}

````grammar
InvariantClause_ =
  "invariant" { Attribute }
  Expression(allowLemma: false, allowLambda: true)
````

#### 29.2.5.9. Reads clauses {#g-reads-clause}

````grammar
ReadsClause(allowLemma, allowLambda, allowWild) =
  "reads"
  { Attribute }
  PossiblyWildFrameExpression(allowLemma, allowLambda, allowWild)
  { "," PossiblyWildFrameExpression(allowLemma, allowLambda, allowWild) }
````

#### 29.2.5.12. Frame expressions {#g-frame-expression}

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

#### 29.2.6.1. Labeled statement {#g-labeled-statement}

````grammar
Stmt = { "label" LabelName ":" } NonLabeledStmt
````

#### 29.2.6.2. Non-Labeled statement {#g-nonlabeled-statement}

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

#### 29.2.6.3. Break and continue statements {#g-break-continue-statement}

````grammar
BreakStmt =
  ( "break" LabelName ";"
  | "continue" LabelName ";"
  | { "break" } "break" ";"
  | { "break" } "continue" ";"
  )
````

#### 29.2.6.4. Block statement {#g-block-statement}

````grammar
BlockStmt = "{" { Stmt } "}"
````

#### 29.2.6.5. Return statement {#g-return-statement}

````grammar
ReturnStmt = "return" [ Rhs { "," Rhs } ] ";"
````

#### 29.2.6.6. Yield statement {#g-yield-statement}

````grammar
YieldStmt = "yield" [ Rhs { "," Rhs } ] ";"
````

#### 29.2.6.7. Update and call statement {#g-update-and-call-statement}

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

#### 29.2.6.8. Update with failure statement {#g-update-with-failure-statement}

````grammar
UpdateFailureStmt  =
    [ Lhs { "," Lhs } ]
    ":-"
    [ "expect"  | "assert" | "assume" ]
    Expression(allowLemma: false, allowLambda: false)
    { "," Rhs }
    ";"
````

#### 29.2.6.9. Variable declaration statement {#g-variable-declaration-statement}

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

CasePatternLocal = ( [ Ident ] "(" CasePatternLocal { "," CasePatternLocal } ")"
                   | LocalIdentTypeOptional
                   )
````

#### 29.2.6.10. Guards {#g-guard}

````grammar
Guard = ( "*"
        | "(" "*" ")"
        | Expression(allowLemma: true, allowLambda: true)
        )
````

#### 29.2.6.11. Binding guards {#g-binding-guard} 

````grammar
BindingGuard(allowLambda) =
  IdentTypeOptional { "," IdentTypeOptional }
  { Attribute }
  ":|"
  Expression(allowLemma: true, allowLambda)
````

#### 29.2.6.12. If statement {#g-if-statement}

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
    BindingGuard(allowLambda: false) // permitted iff allowBindingGuards == true
    | Expression(allowLemma: true, allowLambda: false)
    ) "=>" { Stmt }
  }
````

#### 29.2.6.13. While Statement {#g-while-statement}

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

#### 29.2.6.14. For statement {#g-for-statement}

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

#### 29.2.6.15. Match statement {#g-match-statement}

````grammar
MatchStmt =
  "match"
  Expression(allowLemma: true, allowLambda: true)
  ( "{" { CaseStmt } "}"
  | { CaseStmt }
  )

CaseStmt = "case" ExtendedPattern "=>" { Stmt }
````

#### 29.2.6.16. Assert statement {#g-assert-statement}

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

#### 29.2.6.17. Assume statement {#g-assume-statement}

````grammar
AssumeStmt =
  "assume"
  { Attribute }
  Expression(allowLemma: false, allowLambda: true)
  ";"
````

#### 29.2.6.18. Expect statement {#g-expect-statement}

````grammar
ExpectStmt =
  "expect"
  { Attribute }
  Expression(allowLemma: false, allowLambda: true)
  [ "," Expression(allowLemma: false, allowLambda: true) ]
  ";"
````

#### 29.2.6.19. Print statement {#g-print-statement}

````grammar
PrintStmt =
  "print"
  Expression(allowLemma: false, allowLambda: true)
  { "," Expression(allowLemma: false, allowLambda: true) }
  ";"
````

#### 29.2.6.20. Reveal statement {#g-reveal-statement}

````grammar
RevealStmt =
  "reveal"
  Expression(allowLemma: false, allowLambda: true)
  { "," Expression(allowLemma: false, allowLambda: true) }
  ";"
````
#### 29.2.6.21. Forall statement {#g-forall-statement}

````grammar
ForallStmt =
  "forall"
  ( "(" [ QuantifierDomain ] ")"
  | [ QuantifierDomain ]
  )
  { EnsuresClause(allowLambda: true) }
  [ BlockStmt ]
````
#### 29.2.6.22. Modify statement {#g-modify-statement}

````grammar
ModifyStmt =
  "modify"
  { Attribute }
  FrameExpression(allowLemma: false, allowLambda: true)
  { "," FrameExpression(allowLemma: false, allowLambda: true) }
  ";"
````
#### 29.2.6.23. Calc statement {#g-calc-statement}

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

#### 29.2.7.1. Top-level expression {#g-top-level-expression}

````grammar
Expression(allowLemma, allowLambda) =
  EquivExpression(allowLemma, allowLambda)
  [ ";" Expression(allowLemma, allowLambda) ]
````

The "allowLemma" argument says whether or not the expression
to be parsed is allowed to have the form `S;E` where `S` is a call to a lemma.
"allowLemma" should be passed in as "false" whenever the expression to
be parsed sits in a context that itself is terminated by a semi-colon.

The "allowLambda" says whether or not the expression to be parsed is
allowed to be a lambda expression.  More precisely, an identifier or
parenthesized-enclosed comma-delimited list of identifiers is allowed to
continue as a lambda expression (that is, continue with a `reads`, `requires`,
or `=>`) only if "allowLambda" is true.  This affects function/method/iterator
specifications, if/while statements with guarded alternatives, and expressions
in the specification of a lambda expression itself.

#### 29.2.7.2. Equivalence expression {#g-equivalence-expression}

````grammar
EquivExpression(allowLemma, allowLambda) =
  ImpliesExpliesExpression(allowLemma, allowLambda)
  { "<==>" ImpliesExpliesExpression(allowLemma, allowLambda) }
````

#### 29.2.7.3. Implies expression {#g-implies-expression}

````grammar
ImpliesExpliesExpression(allowLemma, allowLambda) =
  LogicalExpression(allowLemma, allowLambda)
  [ (  "==>" ImpliesExpression(allowLemma, allowLambda)
    | "<==" LogicalExpression(allowLemma, allowLambda)
            { "<==" LogicalExpression(allowLemma, allowLambda) }
    )
  ]

ImpliesExpression(allowLemma, allowLambda) =
  LogicalExpression(allowLemma, allowLambda)
  [  "==>" ImpliesExpression(allowLemma, allowLambda) ]
````

#### 29.2.7.4. Logical expression {#g-logical-expression}

````grammar
LogicalExpression(allowLemma, allowLambda) =
  RelationalExpression(allowLemma, allowLambda)
  [ ( "&&" RelationalExpression(allowLemma, allowLambda)
           { "&&" RelationalExpression(allowLemma, allowLambda) }
    | "||" RelationalExpression(allowLemma, allowLambda)
           { "||" RelationalExpression(allowLemma, allowLambda) }
    )
  ]
  | { "&&" RelationalExpression(allowLemma, allowLambda) }
  | { "||" RelationalExpression(allowLemma, allowLambda) }
````

#### 29.2.7.5. Relational expression {#g-relational-expression}

````grammar
RelationalExpression(allowLemma, allowLambda) =
  ShiftTerm(allowLemma, allowLambda)
  { RelOp ShiftTerm(allowLemma, allowLambda) }

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

#### 29.2.7.6. Bit-shift expression {#g-bit-shift-expression}

````grammar
ShiftTerm(allowLemma, allowLambda) =
  Term(allowLemma, allowLambda)
  { ShiftOp Term(allowLemma, allowLambda) }

ShiftOp = ( "<<" | ">>" )
````

#### 29.2.7.7. Term (addition operations) {#g-term}

````grammar
Term(allowLemma, allowLambda) =
  Factor(allowLemma, allowLambda)
  { AddOp Factor(allowLemma, allowLambda) }

AddOp = ( "+" | "-" )
````

#### 29.2.7.8. Factor (multiplication operations) {#g-factor}

````grammar
Factor(allowLemma, allowLambda) =
  BitvectorFactor(allowLemma, allowLambda)
  { MulOp BitvectorFactor(allowLemma, allowLambda) }

MulOp = ( "*" | "/" | "%" )
````

#### 29.2.7.9. Bit-vector expression {#g-bit-vector-expression}

````grammar
BitvectorFactor(allowLemma, allowLambda) =
  AsExpression(allowLemma, allowLambda)
  { BVOp AsExpression(allowLemma, allowLambda) }

BVOp = ( "|" | "&" | "^" )
````

#### 29.2.7.10. As/Is expression {#g-as-is-expression}

````grammar
AsExpression(allowLemma, allowLambda) =
  UnaryExpression(allowLemma, allowLambda)
  { ( "as" | "is" ) Type }
````

#### 29.2.7.11. Unary expression {#g-unary-expression}
````grammar
UnaryExpression(allowLemma, allowLambda) =
  ( "-" UnaryExpression(allowLemma, allowLambda)
  | "!" UnaryExpression(allowLemma, allowLambda)
  | PrimaryExpression(allowLemma, allowLambda)
  )
````

#### 29.2.7.12. Primary expression {#g-primary-expresson}
````grammar
PrimaryExpression(allowLemma, allowLambda) =
  ( NameSegment { Suffix }
  | LambdaExpression(allowLemma)
  | MapDisplayExpr { Suffix }
  | SeqDisplayExpr { Suffix }
  | SetDisplayExpr { Suffix }
  | EndlessExpression(allowLemma, allowLambda)
  | ConstAtomExpression { Suffix }
  )
````

#### 29.2.7.13. Lambda expression {#g-lambda-expression}
````grammar
LambdaExpression(allowLemma) =
  ( WildIdent
  | "(" [ IdentTypeOptional { "," IdentTypeOptional } ] ")"
  )
  LambdaSpec
  "=>"
  Expression(allowLemma, allowLambda: true)
````

#### 29.2.7.14. Left-hand-side expression {#g-lhs-expression}
````grammar
Lhs =
  ( NameSegment { Suffix }
  | ConstAtomExpression Suffix { Suffix }
  )
````

#### 29.2.7.15. Right-hand-side expression {#g-rhs-expression}
<pre>
Rhs =
  ( <a href="#g-array-allocation-expression">ArrayAllocation_</a>
  | <a href="#g-object-allocation-expression">ObjectAllocation_</a>
  | Expression(allowLemma: false, allowLambda: true)
  | <a href="#g-havoc-expression">HavocRhs_</a>
  )
  { Attribute }
</pre>

#### 29.2.7.16. Array allocation right-hand-side expression {#g-array-allocation-expression}
````grammar
ArrayAllocation_ =
  "new" [ Type ] "[" [ Expressions ] "]"
  [ "(" Expression(allowLemma: true, allowLambda: true) ")"
  | "[" [ Expressions ] "]"
  ]
````

#### 29.2.7.17. Object allocation right-hand-side expression {#g-object-allocation-expression}
````grammar
ObjectAllocation_ = "new" Type [ "." TypeNameOrCtorSuffix ]
                               [ "(" [ Bindings ] ")" ]
````

#### 29.2.7.18. Havoc right-hand-side expression {#g-havoc-expression}
````grammar
HavocRhs_ = "*"
````

#### 29.2.7.19. Atomic expressions {#g-atomic-expression}

````grammar
ConstAtomExpression =
  ( LiteralExpression
  | "this"
  | FreshExpression_
  | AllocatedExpression_
  | UnchangedExpression_
  | OldExpression_
  | CardinalityExpression_
  | ParensExpression
  )
````

#### 29.2.7.19. Literal expressions {#g-literal-expression}

````grammar
LiteralExpression =
 ( "false" | "true" | "null" | Nat | Dec |
   charToken | stringToken )

Nat = ( digits | hexdigits )

Dec = decimaldigits
````

#### 29.2.7.19. Old and Old@ Expressions {#g-old-expression}

````grammar
OldExpression_ =
  "old" [ "@" LabelName ]
  "(" Expression(allowLemma: true, allowLambda: true) ")"
````

#### 29.2.7.19. Fresh Expressions {#g-fresh-expression}

````grammar
FreshExpression_ =
  "fresh" [ "@" LabelName ]
  "(" Expression(allowLemma: true, allowLambda: true) ")"
````

#### 29.2.7.19. Allocated Expressions {#g-allocated-expression}

````grammar
AllocatedExpression_ =
  "allocated" "(" Expression(allowLemma: true, allowLambda: true) ")"
````

#### 29.2.7.19. Unchanged Expressions {#g-unchanged-expression}

````grammar
UnchangedExpression_ =
  "unchanged" [ "@" LabelName ]
  "(" FrameExpression(allowLemma: true, allowLambda: true)
      { "," FrameExpression(allowLemma: true, allowLambda: true) }
  ")"
````

#### 29.2.7.19. Cardinality Expressions {#g-cardinality-expression}

````grammar
CardinalityExpression_ =
  "|" Expression(allowLemma: true, allowLambda: true) "|"
````

#### 29.2.7.19. Parenthesized Expression {#g-parenthesized-expression}

````grammar
ParensExpression =
  "(" [ Expressions ] ")"
````

#### 29.2.7.19. Sequence Display Expression {#g-sequence-display-expression}

````grammar
SeqDisplayExpr =
  ( "[" [ Expressions ] "]"
  | "seq" [ GenericInstantiation ]
    "(" Expression(allowLemma: true, allowLambda: true)
    "," Expression(allowLemma: true, allowLambda: true)
    ")"
  )
````

#### 29.2.7.19. Set Display Expression {#g-set-display-expression}

````grammar
SetDisplayExpr =
  ( [ "iset" | "multiset" ] "{" [ Expressions ] "}"
  | "multiset" "(" Expression(allowLemma: true,
                              allowLambda: true) ")"
  )
````

#### 29.2.7.19. Map Display Expression {#g-map-display-expression}

````grammar
MapDisplayExpr =
  ("map" | "imap" ) "[" [ MapLiteralExpressions ] "]"

MapLiteralExpressions =
  Expression(allowLemma: true, allowLambda: true)
  ":=" Expression(allowLemma: true, allowLambda: true)
  { "," Expression(allowLemma: true, allowLambda: true)
        ":=" Expression(allowLemma: true, allowLambda: true)
  }
````

#### 29.2.7.19. Endless Expression {#g-endless-expression}

````grammar
EndlessExpression(allowLemma, allowLambda) =
  ( IfExpression(allowLemma, allowLambda)
  | MatchExpression(allowLemma, allowLambda)
  | QuantifierExpression(allowLemma, allowLambda)
  | SetComprehensionExpr(allowLemma, allowLambda)
  | StmtInExpr Expression(allowLemma, allowLambda)
  | LetExpression(allowLemma, allowLambda)
  | MapComprehensionExpr(allowLemma, allowLambda)
  )
````

#### 29.2.7.19. If expression {#g-if-expression}

````grammar
IfExpression(allowLemma, allowLambda) =
    "if" ( BindingGuard(allowLambda: true)
         | Expression(allowLemma: true, allowLambda: true)
         )
    "then" Expression(allowLemma: true, allowLambda: true)
    "else" Expression(allowLemma, allowLambda)
````

#### 29.2.7.19. Match Expression {#g-match-expression}

````grammar
MatchExpression(allowLemma, allowLambda) =
  "match" Expression(allowLemma, allowLambda)
  ( "{" { CaseExpression(allowLemma: true, allowLambda: true) } "}"
  | { CaseExpression(allowLemma, allowLambda) }
  )

CaseExpression(allowLemma, allowLambda) =
  "case" { Attribute } ExtendedPattern "=>" Expression(allowLemma, allowLambda)
````

#### 29.2.7.19. Case and Extended Patterns {#g-pattern}

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

#### 29.2.9.19. Quantifier expression {#g-quantifier-expression}

````grammar
QuantifierExpression(allowLemma, allowLambda) =
    ( "forall" | "exists" ) QuantifierDomain "::"
    Expression(allowLemma, allowLambda)
````

#### 29.2.7.19. Set Comprehension Expressions {#g-set-comprehension-expression}

````grammar
SetComprehensionExpr(allowLemma, allowLambda) =
  [ "set" | "iset" ]
  QuantifierDomain(allowLemma, allowLambda)
  [ "::" Expression(allowLemma, allowLambda) ]
````


#### 29.2.7.19. Statements in an Expression {#g-statement-in-expression}

````grammar
StmtInExpr = ( AssertStmt | AssumeStmt | ExpectStmt
             | RevealStmt | CalcStmt
             )
````

#### 29.2.7.19. Let and Let or Fail Expression {#g-let-expression}

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

#### 29.2.7.19. Map Comprehension Expression {#g-map-comprehension-expression}

````grammar
MapComprehensionExpr(allowLemma, allowLambda) =
  ( "map" | "imap" )
  QuantifierDomain(allowLemma, allowLambda)
  "::"
  Expression(allowLemma, allowLambda)
  [ ":=" Expression(allowLemma, allowLambda) ]
````

#### 29.2.7.19. Name Segment {#g-name-segment}

````grammar
NameSegment = Ident [ GenericInstantiation | HashCall ]
````

#### 29.2.7.19. Hash Call {#g-hash-call}

````grammar
HashCall = "#" [ GenericInstantiation ]
  "[" Expression(allowLemma: true, allowLambda: true) "]"
  "(" [ Bindings ] ")"
````

#### 29.2.7.19. Suffix {#g-suffix}

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

#### 29.2.7.19. Augmented Dot Suffix {#g-augmented-dot-suffix}

````grammar
AugmentedDotSuffix_ = "." DotSuffix
                      [ GenericInstantiation | HashCall ]
````

#### 29.2.7.19. Datatype Update Suffix {#g-datatype-update-suffix}

````grammar
DatatypeUpdateSuffix_ =
  "." "(" MemberBindingUpdate { "," MemberBindingUpdate } ")"

MemberBindingUpdate =
  ( ident | digits )
  ":=" Expression(allowLemma: true, allowLambda: true)
````

#### 29.2.7.19. Subsequence Suffix {#g-subsequence-suffix}

````grammar
SubsequenceSuffix_ =
  "[" [ Expression(allowLemma: true, allowLambda: true) ]
      ".." [ Expression(allowLemma: true, allowLambda: true) ]
  "]"
````

#### 29.2.7.19. Subsequence Slices Suffix {#g-subsequence-slices-suffix}

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

#### 29.2.7.19. Sequence Update Suffix {#g-sequence-update-suffix}

````grammar
SequenceUpdateSuffix_ =
  "[" Expression(allowLemma: true, allowLambda: true)
      ":=" Expression(allowLemma: true, allowLambda: true)
  "]"
````

#### 29.2.7.19. Selection Suffix {#g-selection-suffix}

````grammar
SelectionSuffix_ =
  "[" Expression(allowLemma: true, allowLambda: true)
      { "," Expression(allowLemma: true, allowLambda: true) }
  "]"
````

#### 29.2.7.19. Argument List Suffix {#g-argument-list-suffix}

````grammar
ArgumentListSuffix_ = "(" [ Expressions ] ")"
````

#### 29.2.7.19. Expression Lists {#g-expression-list}

````grammar
Expressions =
    Expression(allowLemma: true, allowLambda: true)
    { "," Expression(allowLemma: true, allowLambda: true) }
````

#### 29.2.7.19. Parameter Bindings {#g-parameter-bindings}

````grammar
ActualBindings =
    ActualBinding
    { "," ActualBinding }

ActualBinding =
    [ NoUSIdentOrDigits ":=" ]
    Expression(allowLemma: true, allowLambda: true)
````

#### 29.2.7.19. Quantifier domains {#g-quantifier-domain}

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


#### 29.2.7.19. Basic name and type combinations

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
