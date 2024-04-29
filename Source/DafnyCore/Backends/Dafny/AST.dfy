module {:extern "DAST.Format"} DAST.Format
  /* Cues about how to format different AST elements if necessary,
     e.g. to generate idiomatic code when needed. */
{
  // Dafny AST compilation tenets:
  // - The Compiled Dafny AST should be minimal
  // - The generated code should look idiomatic and close to the original Dafny file if possible
  // Since the two might conflict, the second one is taken care of by adding formatting information

  datatype UnaryOpFormat =
    | NoFormat
    | CombineFormat
  datatype BinaryOpFormat =
    | NoFormat
    | ImpliesFormat
    | EquivalenceFormat
    | ReverseFormat
}

module {:extern "DAST"} DAST {
  import opened Std.Wrappers

  datatype Module = Module(name: string, isExtern: bool, body: seq<ModuleItem>)

  datatype ModuleItem =
    | Module(Module)
    | Class(Class)
    | Trait(Trait)
    | Newtype(Newtype)
    | Datatype(Datatype)

  datatype Type =
    Path(seq<Ident>, typeArgs: seq<Type>, resolved: ResolvedType) |
    Nullable(Type) |
    Tuple(seq<Type>) |
    Array(element: Type, dims: nat) |
    Seq(element: Type) |
    Set(element: Type) |
    Multiset(element: Type) |
    Map(key: Type, value: Type) |
    SetBuilder(element: Type) |
    MapBuilder(key: Type, value: Type) |
    Arrow(args: seq<Type>, result: Type) |
    Primitive(Primitive) | Passthrough(string) |
    TypeArg(Ident)

  datatype Primitive = Int | Real | String | Bool | Char

  datatype NewtypeRange =
    | U8 | I8 | U16 | I16 | U32 | I32 | U64 | I64 | U128 | I128 | BigInt
    | NoRange

  datatype ResolvedType =
    | Datatype(path: seq<Ident>)
    | Trait(path: seq<Ident>)
    | Newtype(baseType: Type, range: NewtypeRange, erase: bool)

  datatype Ident = Ident(id: string)

  datatype Class = Class(name: string, enclosingModule: Ident, typeParams: seq<Type>, superClasses: seq<Type>, fields: seq<Field>, body: seq<ClassItem>)

  datatype Trait = Trait(name: string, typeParams: seq<Type>, body: seq<ClassItem>)

  datatype Datatype = Datatype(name: string, enclosingModule: Ident, typeParams: seq<Type>, ctors: seq<DatatypeCtor>, body: seq<ClassItem>, isCo: bool)

  datatype DatatypeCtor = DatatypeCtor(name: string, args: seq<Formal>, hasAnyArgs: bool /* includes ghost */)

  datatype Newtype = Newtype(name: string, typeParams: seq<Type>, base: Type, range: NewtypeRange, witnessStmts: seq<Statement>, witnessExpr: Option<Expression>)

  datatype ClassItem = Method(Method)

  datatype Field = Field(formal: Formal, defaultValue: Option<Expression>)

  datatype Formal = Formal(name: string, typ: Type)

  datatype Method = Method(isStatic: bool, hasBody: bool, overridingPath: Option<seq<Ident>>, name: string, typeParams: seq<Type>, params: seq<Formal>, body: seq<Statement>, outTypes: seq<Type>, outVars: Option<seq<Ident>>)

  datatype CallName =
    Name(name: string) |
    MapBuilderAdd | MapBuilderBuild | SetBuilderAdd | SetBuilderBuild

  datatype Statement =
    DeclareVar(name: string, typ: Type, maybeValue: Option<Expression>) |
    Assign(lhs: AssignLhs, value: Expression) |
    If(cond: Expression, thn: seq<Statement>, els: seq<Statement>) |
    Labeled(lbl: string, body: seq<Statement>) |
    While(cond: Expression, body: seq<Statement>) |
    Foreach(boundName: string, boundType: Type, over: Expression, body: seq<Statement>) |
    Call(on: Expression, callName: CallName, typeArgs: seq<Type>, args: seq<Expression>, outs: Option<seq<Ident>>) |
    Return(expr: Expression) |
    EarlyReturn() |
    Break(toLabel: Option<string>) |
    TailRecursive(body: seq<Statement>) |
    JumpTailCallStart() |
    Halt() |
    Print(Expression)

  datatype AssignLhs =
    Ident(Ident) |
    Select(expr: Expression, field: string) |
    Index(expr: Expression, indices: seq<Expression>)

  datatype CollKind = Seq | Array | Map

  datatype BinOp =
    Eq(referential: bool, nullable: bool) |
    Div() | EuclidianDiv() |
    Mod() | EuclidianMod() |
    Lt() | // a <= b is !(b < a)
    LtChar() |
    Plus() | Minus() | Times() |
    BitwiseAnd() | BitwiseOr() | BitwiseXor() |
    BitwiseShiftRight() | BitwiseShiftLeft() |
    And() | Or() |
    In() |
    SeqProperPrefix() | SeqPrefix() |
    SetMerge() | SetSubtraction() | SetIntersection() |
    Subset() | ProperSubset() | SetDisjoint() |
    MapMerge() | MapSubtraction() |
    MultisetMerge() | MultisetSubtraction() | MultisetIntersection() |
    Submultiset() | ProperSubmultiset() | MultisetDisjoint() |
    Concat() |
    Passthrough(string)

  datatype Expression =
    Literal(Literal) |
    Ident(string) |
    Companion(seq<Ident>) |
    Tuple(seq<Expression>) |
    New(path: seq<Ident>, typeArgs: seq<Type>, args: seq<Expression>) |
    NewArray(dims: seq<Expression>, typ: Type) |
    DatatypeValue(path: seq<Ident>, typeArgs: seq<Type>, variant: string, isCo: bool, contents: seq<(string, Expression)>) |
    Convert(value: Expression, from: Type, typ: Type) |
    SeqConstruct(length: Expression, elem: Expression) |
    SeqValue(elements: seq<Expression>, typ: Type) |
    SetValue(elements: seq<Expression>) |
    MultisetValue(elements: seq<Expression>) |
    MapValue(mapElems: seq<(Expression, Expression)>) |
    MapBuilder(keyType: Type, valueType: Type) |
    SeqUpdate(expr: Expression, indexExpr: Expression, value: Expression) |
    MapUpdate(expr: Expression, indexExpr: Expression, value: Expression) |
    SetBuilder(elemType: Type) |
    ToMultiset(Expression) |
    This() |
    Ite(cond: Expression, thn: Expression, els: Expression) |
    UnOp(unOp: UnaryOp, expr: Expression, format1: Format.UnaryOpFormat) |
    BinOp(op: BinOp, left: Expression, right: Expression, format2: Format.BinaryOpFormat) |
    ArrayLen(expr: Expression, dim: nat) |
    MapKeys(expr: Expression) |
    MapValues(expr: Expression) |
    Select(expr: Expression, field: string, isConstant: bool, onDatatype: bool) |
    SelectFn(expr: Expression, field: string, onDatatype: bool, isStatic: bool, arity: nat) |
    Index(expr: Expression, collKind: CollKind, indices: seq<Expression>) |
    IndexRange(expr: Expression, isArray: bool, low: Option<Expression>, high: Option<Expression>) |
    TupleSelect(expr: Expression, index: nat) |
    Call(on: Expression, callName: CallName, typeArgs: seq<Type>, args: seq<Expression>) |
    Lambda(params: seq<Formal>, retType: Type, body: seq<Statement>) |
    BetaRedex(values: seq<(Formal, Expression)>, retType: Type, expr: Expression) |
    IIFE(name: Ident, typ: Type, value: Expression, iifeBody: Expression) |
    Apply(expr: Expression, args: seq<Expression>) |
    TypeTest(on: Expression, dType: seq<Ident>, variant: string) |
    InitializationValue(typ: Type) |
    BoolBoundedPool() |
    SetBoundedPool(of: Expression) |
    SeqBoundedPool(of: Expression, includeDuplicates: bool) |
    IntRange(lo: Expression, hi: Expression)

  datatype UnaryOp = Not | BitwiseNot | Cardinality

  datatype Literal = BoolLiteral(bool) | IntLiteral(string, Type) | DecLiteral(string, string, Type) | StringLiteral(string) | CharLiteral(char) | Null(Type)
}
