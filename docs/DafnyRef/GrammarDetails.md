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

#### 29.2.1.1. Top-level declarations {g-top-level-declaration}

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

#### 29.2.1.1. Declaration modifiers {#g-declaration-modifiers}

````grammar
DeclModifier = ( "abstract" | "ghost" | "static" )
````

### 29.2.1. Modules {#g-module}

````grammar
SubModuleDecl = ( ModuleDefinition | ModuleImport | ModuleExport )
````

#### 29.2.1.1. Module Definitions {#g-module-definition}

````grammar
ModuleDefinition = "module" { Attribute } ModuleQualifiedName
        [ "refines" ModuleQualifiedName ]
        "{" { TopDecl } "}"
````

#### 29.2.1.1. Module Imports {#g-module-import}

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

#### 29.2.1.3. Module Export Definitions {#g-module-export}

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



### 29.2.1. Expressions

#### 29.2.1.1. Top-level expression {#g-top-level-expression}

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

#### 29.2.1.2. Equivalence expression {#g-equivalence-expression}

````grammar
EquivExpression(allowLemma, allowLambda) =
  ImpliesExpliesExpression(allowLemma, allowLambda)
  { "<==>" ImpliesExpliesExpression(allowLemma, allowLambda) }
````

#### 29.2.1.3. Implies expression {#g-implies-expression}

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

#### 29.2.1.4. Logical expression {#g-logical-expression}

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

#### 29.2.1.5. Relational expression {#g-relational-expression}

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

#### 29.2.1.6. Bit-shift expression {#g-bit-shift-expression}

````grammar
ShiftTerm(allowLemma, allowLambda) =
  Term(allowLemma, allowLambda)
  { ShiftOp Term(allowLemma, allowLambda) }

ShiftOp = ( "<<" | ">>" )
````

#### 29.2.1.7. Term (addition operations) {#g-term}

````grammar
Term(allowLemma, allowLambda) =
  Factor(allowLemma, allowLambda)
  { AddOp Factor(allowLemma, allowLambda) }

AddOp = ( "+" | "-" )
````

#### 29.2.1.8. Factor (multiplication operations) {#g-factor}

````grammar
Factor(allowLemma, allowLambda) =
  BitvectorFactor(allowLemma, allowLambda)
  { MulOp BitvectorFactor(allowLemma, allowLambda) }

MulOp = ( "*" | "/" | "%" )
````

#### 29.2.1.9. Bit-vector expression {#g-bit-vector-expression}

````grammar
BitvectorFactor(allowLemma, allowLambda) =
  AsExpression(allowLemma, allowLambda)
  { BVOp AsExpression(allowLemma, allowLambda) }

BVOp = ( "|" | "&" | "^" )
````

#### 29.2.1.10. As/Is expression {#g-as-is-expression}

````grammar
AsExpression(allowLemma, allowLambda) =
  UnaryExpression(allowLemma, allowLambda)
  { ( "as" | "is" ) Type }
````

#### 29.2.1.11. Unary expression {#g-unary-expression}
````grammar
UnaryExpression(allowLemma, allowLambda) =
  ( "-" UnaryExpression(allowLemma, allowLambda)
  | "!" UnaryExpression(allowLemma, allowLambda)
  | PrimaryExpression(allowLemma, allowLambda)
  )
````

#### 29.2.1.12. Primary expression {#g-primary-expresson}
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

#### 29.2.1.13. Lambda expression {#g-lambda-expression}
````grammar
LambdaExpression(allowLemma) =
  ( WildIdent
  | "(" [ IdentTypeOptional { "," IdentTypeOptional } ] ")"
  )
  LambdaSpec
  "=>"
  Expression(allowLemma, allowLambda: true)
````

#### Left-hand-side expression {g-lhs-expression}
````grammar
Lhs =
  ( NameSegment { Suffix }
  | ConstAtomExpression Suffix { Suffix }
  )
````

#### Right-hand-side expression {#g-rhs-expression}
<pre>
Rhs =
  ( <a href="#g-array-allocation-expression">ArrayAllocation_</a>
  | <a href="#g-object-allocation-expression">ObjectAllocation_</a>
  | Expression(allowLemma: false, allowLambda: true)
  | <a href="#g-havoc-expression">HavocRhs_</a>
  )
  { Attribute }
</pre>

#### Array allocation right-hand-side expression {#g-array-allocation-expression}
````grammar
ArrayAllocation_ =
  "new" [ Type ] "[" [ Expressions ] "]"
  [ "(" Expression(allowLemma: true, allowLambda: true) ")"
  | "[" [ Expressions ] "]"
  ]
````

#### Object allocation right-hand-side expression {#g-object-allocation-expression}
````grammar
ObjectAllocation_ = "new" Type [ "." TypeNameOrCtorSuffix ]
                               [ "(" [ Bindings ] ")" ]
````

#### Havoc right-hand-side expression (#g-havoc-expression}
````grammar
HavocRhs_ = "*"
````

