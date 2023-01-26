# 29. Dafny Grammar

The Dafny parser is generated from a grammar definition file, `Dafny.atg` by the [CoCo/r](https://ssw.jku.at/Research/Projects/Coco/)
parser generator.

The grammar has a traditional structure: a scanner tokenizes the textual input into a sequence of tokens; the parser consumes the tokens
to produce an AST. The AST is then passed on for name and type resolution and further processing.


## 29.1. Dafny Syntax


## 29.2. Dafny Grammar productions

### 29.2.1. Programs {#g-program}

````grammar
Dafny = { IncludeDirective_ } { TopDecl } EOF
````

#### 29.2.1.1. Include directives {#g-include-directive}

````grammar
IncludeDirective_ = "include" stringToken
````

#### 29.2.1.2. Top-level declarations {g-top-level-declaration}

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
ModuleDefinition = "module" { Attribute } ModuleQualifiedName
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


### 29.2.3. Specifications

#### 29.2.3.1. Method specifications {#g-method-specification}

````grammar
MethodSpec =
  { ModifiesClause(allowLambda: false)
  | RequiresClause(allowLabel: true)
  | EnsuresClause(allowLambda: false)
  | DecreasesClause(allowWildcard: true, allowLambda: false)
  }
````

#### 29.2.3.2. Function specifications {#g-function-specification}

````grammar
FunctionSpec =
  { RequiresClause(allowLabel: true)
  | ReadsClause(allowLemma: false, allowLambda: false, allowWild: true)
  | EnsuresClause(allowLambda: false)
  | DecreasesClause(allowWildcard: false, allowLambda: false)
  }
````

#### 29.2.3.3. Lambda function specifications {#g-lambda-specification}

````grammar
LambdaSpec =
  { ReadsClause(allowLemma: true, allowLambda: false, allowWild: true)
  | "requires" Expression(allowLemma: false, allowLambda: false)
  }
````

#### 29.2.3.4. Iterator specifications {#g-iterator-specification}

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

#### 29.2.3.5. Loop specifications {#g-loop-specification}

````grammar
LoopSpec =
  { InvariantClause_
  | DecreasesClause(allowWildcard: true, allowLambda: true)
  | ModifiesClause(allowLambda: true)
  }
````



#### 29.2.3.6. Requires clauses {#g-requires-clause}

````grammar
RequiresClause(allowLabel) =
  "requires" { Attribute }
  [ LabelName ":" ]  // Label allowed only if allowLabel is true
  Expression(allowLemma: false, allowLambda: false)
````

#### 29.2.3.7. Ensures clauses {#g-ensures-clause}

````grammar
EnsuresClause(allowLambda) =
  "ensures" { Attribute } Expression(allowLemma: false, allowLambda)
````

#### 29.2.3.8. Decreases clauses {#g-decreases-clause}

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

#### 29.2.3.9. Reads clauses {#g-reads-clause}

````grammar
ReadsClause(allowLemma, allowLambda, allowWild) =
  "reads"
  { Attribute }
  PossiblyWildFrameExpression(allowLemma, allowLambda, allowWild)
  { "," PossiblyWildFrameExpression(allowLemma, allowLambda, allowWild) }
````

#### 29.2.3.10. Modifies clauses {#g-modifies-clause}

````grammar
ModifiesClause(allowLambda) =
  "modifies" { Attribute }
  FrameExpression(allowLemma: false, allowLambda)
  { "," FrameExpression(allowLemma: false, allowLambda) }
````

#### 29.2.3.11. Invariant clauses {#g-invariant-clause}

````grammar
InvariantClause_ =
  "invariant" { Attribute }
  Expression(allowLemma: false, allowLambda: true)
````

#### 29.2.3.12. Frame expressions {#g-frame-expression}

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






### 29.2.19. Statements {#g-statement}

#### 29.2.19.1. Labeled statement {#g-labeled-statement}

````grammar
Stmt = { "label" LabelName ":" } NonLabeledStmt
````

#### 29.2.19.1. Non-Labeled statement {#g-nonlabeled-statement}

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

#### 29.2.19.2. Break and continue statements {#g-break-continue-statement}

````grammar
BreakStmt =
  ( "break" LabelName ";"
  | "continue" LabelName ";"
  | { "break" } "break" ";"
  | { "break" } "continue" ";"
  )
````

#### 29.2.19.3. Block statement {#g-block-statement}

````grammar
BlockStmt = "{" { Stmt } "}"
````

#### 29.2.19.4. Return statement {#g-return-statement}

````grammar
ReturnStmt = "return" [ Rhs { "," Rhs } ] ";"
````

#### 29.2.19.5. Yield statement {#g-yield-statement}

````grammar
YieldStmt = "yield" [ Rhs { "," Rhs } ] ";"
````

#### 20.2.19.6. Update and call staetment {#g-update-and-call-statement}

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

#### 20.2.19.7. Update with failure statement {#g-update-with-failure-statement)

````grammar
UpdateFailureStmt  =
    [ Lhs { "," Lhs } ]
    ":-"
    [ "expect"  | "assert" | "assume" ]
    Expression(allowLemma: false, allowLambda: false)
    { "," Rhs }
    ";"
````

#### 20.2.19.8. Variable declaration statement {#g-variable-declaration-statement}

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

CasePatternLocal = ( [ Ident ] "(" CasePatternLocsl { "," CasePatternLocal } ")"
                   | LocalIdentTypeOptional
                   )
````

#### 20.3.19.9. Guards {#g-guard}

````grammar
Guard = ( "*"
        | "(" "*" ")"
        | Expression(allowLemma: true, allowLambda: true)
        )
````

#### 20.3.19.20. Binding guards {#g-binding-guard} 

````grammar
BindingGuard(allowLambda) =
  IdentTypeOptional { "," IdentTypeOptional }
  { Attribute }
  ":|"
  Expression(allowLemma: true, allowLambda)
````

#### 20.2.19.21. If statement {#g-if-statement)

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
      ) "=>" { Stmt } } .
````

#### 20.2.19.22. While Statement {#g-while-statement}

````grammar
WhileStmt =
  "while"
  ( LoopSpec
    AlternativeBlock(allowBindingGuards: false)
  | Guard
    LoopSpec
    ( BlockStmt
    | /* go body-less */
    )
  )
````

#### 20.2.19.23. For statement {#g-for-statement}

````grammar
ForLoopStmt =
  "for" IdentTypeOptional ":="
    Expression(allowLemma: false, allowLambda: false)
    ( "to" | "downto" )
    ( Expression(allowLemma: false, allowLambda: false)
    | "*"
    )
    LoopSpec
    ( BlockStmt
    | /* go body-less */
    )
  )
````

#### 20.2.19.24. Match statement {#g-match-statement}

````grammar
MatchStmt =
  "match"
  Expression(allowLemma: true, allowLambda: true)
  ( "{" { CaseStmt } "}"
  | { CaseStmt }
  )

CaseStmt = "case" ExtendedPattern "=>" { Stmt }
````

#### 20.2.19.25. Assert statement {#g-assert-statement}

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

#### 20.2.19.25. Assume statement {#g-assume-statement}

````grammar
AssumeStmt =
    "assume"
    { Attribute }
    ( Expression(allowLemma: false, allowLambda: true)
    )
    ";"
````

#### 20.2.19.26. Expect statement {#g-expect-statement}

````grammar
ExpectStmt =
    "expect"
    { Attribute }
    ( Expression(allowLemma: false, allowLambda: true)
    )
    [ "," Expression(allowLemma: false, allowLambda: true) ]
    ";"
````

#### 20.2.19.27. Print statement {#g-print-statement}

````grammar
PrintStmt =
    "print"
    Expression(allowLemma: false, allowLambda: true)
    { "," Expression(allowLemma: false, allowLambda: true) }
    ";"
````

#### 20.2.19.28. Reveal statement {#g-reveal-staetment}

````grammar
RevealStmt =
    "reveal"
    Expression(allowLemma: false, allowLambda: true)
    { "," Expression(allowLemma: false, allowLambda: true) }
    ";"
````
#### 20.2.19.29. Forall stastement {#g-forall-statement}

````grammar
ForallStmt =
  "forall"
  ( "(" [ QuantifierDomain ] ")"
  | [ QuantifierDomain ]
  )
  { EnsuresClause(allowLambda: true) }
  [ BlockStmt ]
````
#### 20.2.19.30. Modify statement {#g-modify-statement}

````grammar
ModifyStmt =
  "modify"
  { Attribute }
  FrameExpression(allowLemma: false, allowLambda: true)
  { "," FrameExpression(allowLemma: false, allowLambda: true) }
  ";"
````
#### 20.2.19.31. Calc statement {#g-calc-statement}

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






### 29.2.20. Expressions

#### 29.2.4.1. Top-level expression {#g-top-level-expression}

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

#### 29.2.4.2. Equivalence expression {#g-equivalence-expression}

````grammar
EquivExpression(allowLemma, allowLambda) =
  ImpliesExpliesExpression(allowLemma, allowLambda)
  { "<==>" ImpliesExpliesExpression(allowLemma, allowLambda) }
````

#### 29.2.4.3. Implies expression {#g-implies-expression}

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

#### 29.2.4.4. Logical expression {#g-logical-expression}

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

#### 29.2.4.5. Relational expression {#g-relational-expression}

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

#### 29.2.4.6. Bit-shift expression {#g-bit-shift-expression}

````grammar
ShiftTerm(allowLemma, allowLambda) =
  Term(allowLemma, allowLambda)
  { ShiftOp Term(allowLemma, allowLambda) }

ShiftOp = ( "<<" | ">>" )
````

#### 29.2.4.7. Term (addition operations) {#g-term}

````grammar
Term(allowLemma, allowLambda) =
  Factor(allowLemma, allowLambda)
  { AddOp Factor(allowLemma, allowLambda) }

AddOp = ( "+" | "-" )
````

#### 29.2.4.8. Factor (multiplication operations) {#g-factor}

````grammar
Factor(allowLemma, allowLambda) =
  BitvectorFactor(allowLemma, allowLambda)
  { MulOp BitvectorFactor(allowLemma, allowLambda) }

MulOp = ( "*" | "/" | "%" )
````

#### 29.2.4.9. Bit-vector expression {#g-bit-vector-expression}

````grammar
BitvectorFactor(allowLemma, allowLambda) =
  AsExpression(allowLemma, allowLambda)
  { BVOp AsExpression(allowLemma, allowLambda) }

BVOp = ( "|" | "&" | "^" )
````

#### 29.2.4.10. As/Is expression {#g-as-is-expression}

````grammar
AsExpression(allowLemma, allowLambda) =
  UnaryExpression(allowLemma, allowLambda)
  { ( "as" | "is" ) Type }
````

#### 29.2.4.11. Unary expression {#g-unary-expression}
````grammar
UnaryExpression(allowLemma, allowLambda) =
  ( "-" UnaryExpression(allowLemma, allowLambda)
  | "!" UnaryExpression(allowLemma, allowLambda)
  | PrimaryExpression(allowLemma, allowLambda)
  )
````

#### 29.2.4.12. Primary expression {#g-primary-expresson}
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

#### 29.2.4.13. Lambda expression {#g-lambda-expression}
````grammar
LambdaExpression(allowLemma) =
  ( WildIdent
  | "(" [ IdentTypeOptional { "," IdentTypeOptional } ] ")"
  )
  LambdaSpec
  "=>"
  Expression(allowLemma, allowLambda: true)
````

#### 29.2.4.14. Left-hand-side expression {g-lhs-expression}
````grammar
Lhs =
  ( NameSegment { Suffix }
  | ConstAtomExpression Suffix { Suffix }
  )
````

#### 29.2.4.15. Right-hand-side expression {#g-rhs-expression}
<pre>
Rhs =
  ( <a href="#g-array-allocation-expression">ArrayAllocation_</a>
  | <a href="#g-object-allocation-expression">ObjectAllocation_</a>
  | Expression(allowLemma: false, allowLambda: true)
  | <a href="#g-havoc-expression">HavocRhs_</a>
  )
  { Attribute }
</pre>

#### 29.2.4.16. Array allocation right-hand-side expression {#g-array-allocation-expression}
````grammar
ArrayAllocation_ =
  "new" [ Type ] "[" [ Expressions ] "]"
  [ "(" Expression(allowLemma: true, allowLambda: true) ")"
  | "[" [ Expressions ] "]"
  ]
````

#### 29.2.4.17. Object allocation right-hand-side expression {#g-object-allocation-expression}
````grammar
ObjectAllocation_ = "new" Type [ "." TypeNameOrCtorSuffix ]
                               [ "(" [ Bindings ] ")" ]
````

#### 29.2.4.18. Havoc right-hand-side expression (#g-havoc-expression}
````grammar
HavocRhs_ = "*"
````
