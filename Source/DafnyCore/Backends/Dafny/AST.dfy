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

  function SeqToHeight<T>(s: seq<T>, f: T --> nat): (r: nat)
    requires forall t <- s :: f.requires(t)
    ensures forall t <- s :: f(t) <= r
  {
    if |s| == 0 then 0 else
    var i := f(s[0]);
    var j := SeqToHeight(s[1..], f);
    if i < j then j else i
  }
}

module {:extern "DAST"} DAST {
  import opened Std.Wrappers
  import Std

  // Prevents Dafny names to being direclty integrated into Rust without explicit conversion
  // Make it a newtype once newtypes are compatible with standard library
  // See issue https://github.com/dafny-lang/dafny/issues/5345
  datatype Name = Name(dafny_name: string)

  datatype Module = Module(name: Name, attributes: seq<Attribute>, body: Option<seq<ModuleItem>>)

  datatype ModuleItem =
    | Module(Module)
    | Class(Class)
    | Trait(Trait)
    | Newtype(Newtype)
    | SynonymType(SynonymType)
    | Datatype(Datatype)

  datatype Type =
    UserDefined(resolved: ResolvedType) |
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
    TypeArg(Ident) | Object()
  {
    function Replace(mapping: map<Type, Type>): Type {
      if this in mapping then mapping[this] else
      match this {
        case UserDefined(resolved: ResolvedType) =>
          Type.UserDefined(resolved.Replace(mapping))
        case Tuple(arguments) =>
          Type.Tuple(Std.Collections.Seq.Map(
                       t requires t in arguments => t.Replace(mapping), arguments))
        case Array(element, dims) =>
          Type.Array(element.Replace(mapping), dims)
        case Seq(element) =>
          Type.Seq(element.Replace(mapping))
        case Set(element) =>
          Type.Set(element.Replace(mapping))
        case Multiset(element) =>
          Type.Multiset(element.Replace(mapping))
        case Map(key, value) =>
          Type.Map(key.Replace(mapping), value.Replace(mapping))
        case SetBuilder(element) =>
          Type.SetBuilder(element.Replace(mapping))
        case MapBuilder(key, value) =>
          Type.MapBuilder(key.Replace(mapping), value.Replace(mapping))
        case Arrow(args: seq<Type>, result: Type) =>
          Type.Arrow(Std.Collections.Seq.Map(
                       t requires t in args => t.Replace(mapping), args), result.Replace(mapping))
        case Primitive(_) | Passthrough(_) | Object() | TypeArg(_) =>
          this
      }
    }
  }

  datatype Variance =
    | Nonvariant
    | Covariant
    | Contravariant

  datatype TypeArgDecl = TypeArgDecl(name: Ident, bounds: seq<TypeArgBound>, variance: Variance)

  datatype TypeArgBound =
    | SupportsEquality
    | SupportsDefault

  datatype Primitive = Int | Real | String | Bool | Char

  datatype NewtypeRange =
    | U8 | I8 | U16 | I16 | U32 | I32 | U64 | I64 | U128 | I128 | BigInt
    | NoRange

  datatype Attribute = Attribute(name: string, args: seq<string>)

  datatype DatatypeType = DatatypeType()

  datatype TraitType = TraitType()

  datatype NewtypeType = NewtypeType(baseType: Type, range: NewtypeRange, erase: bool)

  datatype ResolvedTypeBase =
    | Class()
    | Datatype(variances: seq<Variance>)
    | Trait()
    | Newtype(baseType: Type, range: NewtypeRange, erase: bool)

  datatype ResolvedType = ResolvedType(
    path: seq<Ident>,
    typeArgs: seq<Type>,
    kind: ResolvedTypeBase,
    attributes: seq<Attribute>,
    properMethods: seq<Ident>,
    extendedTypes: seq<Type>) {
    function Replace(mapping: map<Type, Type>): ResolvedType {
      ResolvedType(
        path,
        Std.Collections.Seq.Map(
          t requires t in typeArgs => t.Replace(mapping), typeArgs),
        match kind {
          case Newtype(baseType, range, erase) =>
            ResolvedTypeBase.Newtype(baseType.Replace(mapping), range, erase)
          case _ => kind
        },
        attributes,
        properMethods,
        Std.Collections.Seq.Map(
          t requires t in extendedTypes => t.Replace(mapping), extendedTypes)
      )
    }
  }

  datatype Ident = Ident(id: Name)

  datatype Class = Class(name: Name, enclosingModule: Ident, typeParams: seq<TypeArgDecl>, superClasses: seq<Type>, fields: seq<Field>, body: seq<ClassItem>, attributes: seq<Attribute>)

  datatype Trait = Trait(name: Name, typeParams: seq<TypeArgDecl>, parents: seq<Type>, body: seq<ClassItem>, attributes: seq<Attribute>)

  datatype Datatype = Datatype(name: Name, enclosingModule: Ident, typeParams: seq<TypeArgDecl>, ctors: seq<DatatypeCtor>, body: seq<ClassItem>, isCo: bool, attributes: seq<Attribute>)

  datatype DatatypeDtor = DatatypeDtor(formal: Formal, callName: Option<string>)

  datatype DatatypeCtor = DatatypeCtor(name: Name, args: seq<DatatypeDtor>, hasAnyArgs: bool /* includes ghost */)

  datatype Newtype =
    Newtype(
      name: Name, typeParams: seq<TypeArgDecl>, base: Type,
      range: NewtypeRange, constraint: Option<NewtypeConstraint>,
      witnessStmts: seq<Statement>, witnessExpr: Option<Expression>, attributes: seq<Attribute>)

  datatype NewtypeConstraint = NewtypeConstraint(variable: Formal, constraintStmts: seq<Statement>)

  // At this point, constraints have been entirely removed,
  // but synonym types might have different witnesses to use for by the compiler
  datatype SynonymType = SynonymType(name: Name, typeParams: seq<TypeArgDecl>, base: Type, witnessStmts: seq<Statement>, witnessExpr: Option<Expression>, attributes: seq<Attribute>)

  datatype ClassItem = Method(Method)

  datatype Field = Field(formal: Formal, defaultValue: Option<Expression>)

  datatype Formal = Formal(name: Name, typ: Type, attributes: seq<Attribute>)

  datatype Method = Method(
    isStatic: bool,
    hasBody: bool,
    outVarsAreUninitFieldsToAssign: bool, // For constructors
    wasFunction: bool, // To choose between "&self" and "&mut self"
    overridingPath: Option<seq<Ident>>,
    name: Name,
    typeParams: seq<TypeArgDecl>,
    params: seq<Formal>,
    body: seq<Statement>,
    outTypes: seq<Type>,
    outVars: Option<seq<Ident>>)

  datatype CallSignature = CallSignature(parameters: seq<Formal>)

  datatype CallName =
    CallName(name: Name, onType: Option<Type>, receiverArgs: Option<Formal>, signature: CallSignature) |
    MapBuilderAdd | MapBuilderBuild | SetBuilderAdd | SetBuilderBuild

  datatype Statement =
    DeclareVar(name: Name, typ: Type, maybeValue: Option<Expression>) |
    Assign(lhs: AssignLhs, value: Expression) |
    If(cond: Expression, thn: seq<Statement>, els: seq<Statement>) |
    Labeled(lbl: string, body: seq<Statement>) |
    While(cond: Expression, body: seq<Statement>) |
    Foreach(boundName: Name, boundType: Type, over: Expression, body: seq<Statement>) |
    Call(on: Expression, callName: CallName, typeArgs: seq<Type>, args: seq<Expression>, outs: Option<seq<Ident>>) |
    Return(expr: Expression) |
    EarlyReturn() |
    Break(toLabel: Option<string>) |
    TailRecursive(body: seq<Statement>) |
    JumpTailCallStart() |
    Halt() |
    Print(Expression) |
    ConstructorNewSeparator(fields: seq<Formal>)
  {
  }

  datatype AssignLhs =
    Ident(ident: Ident) |
    Select(expr: Expression, field: Name) |
    Index(expr: Expression, indices: seq<Expression>)

  datatype CollKind = Seq | Array | Map

  datatype BinOp =
    Eq(referential: bool) |
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
    Ident(name: Name) |
    Companion(seq<Ident>, typeArgs: seq<Type>) |
    Tuple(seq<Expression>) |
    New(path: seq<Ident>, typeArgs: seq<Type>, args: seq<Expression>) |
    NewUninitArray(dims: seq<Expression>, typ: Type) |
    ArrayIndexToInt(value: Expression) |
    FinalizeNewArray(value: Expression, typ: Type) |
    DatatypeValue(datatypeType: ResolvedType, typeArgs: seq<Type>, variant: Name, isCo: bool, contents: seq<(string, Expression)>) |
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
    ArrayLen(expr: Expression, exprType: Type, dim: nat, native: bool) |
    MapKeys(expr: Expression) |
    MapValues(expr: Expression) |
    Select(expr: Expression, field: Name, isConstant: bool, onDatatype: bool, fieldType: Type) |
    SelectFn(expr: Expression, field: Name, onDatatype: bool, isStatic: bool, arity: nat) |
    Index(expr: Expression, collKind: CollKind, indices: seq<Expression>) |
    IndexRange(expr: Expression, isArray: bool, low: Option<Expression>, high: Option<Expression>) |
    TupleSelect(expr: Expression, index: nat, fieldType: Type) |
    Call(on: Expression, callName: CallName, typeArgs: seq<Type>, args: seq<Expression>) |
    Lambda(params: seq<Formal>, retType: Type, body: seq<Statement>) |
    BetaRedex(values: seq<(Formal, Expression)>, retType: Type, expr: Expression) |
    IIFE(ident: Ident, typ: Type, value: Expression, iifeBody: Expression) |
    Apply(expr: Expression, args: seq<Expression>) |
    TypeTest(on: Expression, dType: seq<Ident>, variant: Name) |
    InitializationValue(typ: Type) |
    BoolBoundedPool() |
    SetBoundedPool(of: Expression) |
    MapBoundedPool(of: Expression) |
    SeqBoundedPool(of: Expression, includeDuplicates: bool) |
    IntRange(lo: Expression, hi: Expression, up: bool) |
    UnboundedIntRange(start: Expression, up: bool) |
    Quantifier(elemType: Type, collection: Expression, is_forall: bool, lambda: Expression)

  datatype UnaryOp = Not | BitwiseNot | Cardinality

  datatype Literal =
    | BoolLiteral(bool)
    | IntLiteral(string, Type)
    | DecLiteral(string, string, Type)
    | StringLiteral(string, verbatim: bool)
    | CharLiteral(char)
    | CharLiteralUTF16(nat)
    | Null(Type)
}
