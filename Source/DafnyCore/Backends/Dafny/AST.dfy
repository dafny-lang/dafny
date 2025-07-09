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

  // A special Dafny name wrapper for variable names.
  // For example, the identifier 'None' needs to be escaped in Rust, but not as a constructor.
  datatype VarName = VarName(dafny_name: string)

  datatype Module = Module(
    name: Name,
    docString: string,
    attributes: seq<Attribute>,
    requiresExterns: bool,
    body: Option<seq<ModuleItem>>)

  datatype ModuleItem =
    | Module(Module)
    | Class(Class)
    | Trait(Trait)
    | Newtype(Newtype)
    | SynonymType(SynonymType)
    | Datatype(Datatype)
  {
    function name(): Name {
      match this {
        case Module(m) => m.name
        case Class(m) => m.name
        case Trait(m) => m.name
        case Newtype(m) => m.name
        case SynonymType(m) => m.name
        case Datatype(m) => m.name
      }
    }
    function attributes(): seq<Attribute> {
      match this {
        case Module(m) => m.attributes
        case Class(m) => m.attributes
        case Trait(m) => m.attributes
        case Newtype(m) => m.attributes
        case SynonymType(m) => m.attributes
        case Datatype(m) => m.attributes
      }
    }
  }

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

    predicate IsPrimitiveInt() {
      match this {
        case Primitive(Int) => true
        case UserDefined(ResolvedType(_, _, SynonymType(typ), _, _, _)) =>
          typ.IsPrimitiveInt()
        case _ => false
      }
    }

    predicate IsGeneralTrait() {
      match this {
        case UserDefined(ResolvedType(_, _, typeKind, _, _, _)) =>
          match typeKind {
            case SynonymType(typ) =>
              typ.IsGeneralTrait()
            case Trait(GeneralTrait) => true
            case _ => false
          }
        case _ => false
      }
    }

    function GetGeneralTraitType(): (r: Type)
      requires IsGeneralTrait()
      ensures r.UserDefined? && r.resolved.kind == ResolvedTypeBase.Trait(GeneralTrait)
    {
      match this {
        case UserDefined(ResolvedType(_, _, typeKind, _, _, _)) =>
          match typeKind {
            case SynonymType(typ) =>
              typ.GetGeneralTraitType()
            case _ => this
          }
      }
    }

    predicate IsClassOrObjectTrait() {
      match this {
        case UserDefined(ResolvedType(_, _, base, _, _, _)) =>
          base.Class? || (base.Trait? && base.traitType.ObjectTrait?)
        case _ => false
      }
    }

    predicate IsDatatype() {
      match this {
        case UserDefined(ResolvedType(_, _, typeKind, _, _, _)) =>
          match typeKind {
            case SynonymType(typ) =>
              typ.IsDatatype()
            case Datatype(_, _) => true
            case _ => false
          }
        case _ => false
      }
    }

    function GetDatatypeType(): (r: Type)
      requires IsDatatype()
      ensures r.UserDefined? && r.resolved.kind.Datatype?
    {
      match this {
        case UserDefined(ResolvedType(_, _, typeKind, _, _, _)) =>
          match typeKind {
            case SynonymType(typ) =>
              typ.GetDatatypeType()
            case _ => this
          }
      }
    }

    // Works well without diamond inheritance. If the case arise, we will need to memoize this function
    // or ensure extendedTypes contains all supertypes.
    predicate Extends(other: Type)
      ensures this.Extends(other) ==> other < this
    {
      match this {
        case UserDefined(ResolvedType(_, _, _, _, _, extendedTypes)) =>
          other in extendedTypes || exists i | 0 <= i < |extendedTypes| :: extendedTypes[i].Extends(other)
        case _ => false
      }
    }

    function RemoveSynonyms(): Type {
      match this {
        case UserDefined(ResolvedType(path, typeArgs, typeKind, attributes, properMethods, extendedTypes)) =>
          match typeKind {
            case SynonymType(typ) =>
              typ.RemoveSynonyms()
            case _ =>
              var newtypeArgs := seq(|typeArgs|, i requires 0 <= i < |typeArgs| => typeArgs[i].RemoveSynonyms());
              UserDefined(ResolvedType(path, newtypeArgs, typeKind, attributes, properMethods, extendedTypes))
          }
        case Tuple(arguments) =>
          Type.Tuple(Std.Collections.Seq.Map(
                       t requires t in arguments => t.RemoveSynonyms(), arguments))
        case Array(element, dims) =>
          Type.Array(element.RemoveSynonyms(), dims)
        case Seq(element) =>
          Type.Seq(element.RemoveSynonyms())
        case Set(element) =>
          Type.Set(element.RemoveSynonyms())
        case Multiset(element) =>
          Type.Multiset(element.RemoveSynonyms())
        case Map(key, value) =>
          Type.Map(key.RemoveSynonyms(), value.RemoveSynonyms())
        case SetBuilder(element) =>
          Type.SetBuilder(element.RemoveSynonyms())
        case MapBuilder(key, value) =>
          Type.MapBuilder(key.RemoveSynonyms(), value.RemoveSynonyms())
        case Arrow(args: seq<Type>, result: Type) =>
          Type.Arrow(Std.Collections.Seq.Map(
                       t requires t in args => t.RemoveSynonyms(), args), result.RemoveSynonyms())
        case Primitive(_) | Passthrough(_) | Object() | TypeArg(_) =>
          this
      }
    }
  }

  datatype Variance =
    | Nonvariant
    | Covariant
    | Contravariant

  datatype TypeArgDecl = TypeArgDecl(
    name: Ident,
    bounds: seq<TypeArgBound>,
    info: TypeParameterInfo)

  datatype TypeArgBound =
    | SupportsEquality
    | SupportsDefault
    | TraitBound(typ: Type)

  datatype Primitive = Int | Real | String | Bool | Char | Native


  datatype NewtypeRange =
    | U8(overflow: bool) // Whether arithmetic operations can overflow and wrap
    | I8(overflow: bool)
    | U16(overflow: bool)
    | I16(overflow: bool)
    | U32(overflow: bool)
    | I32(overflow: bool)
    | U64(overflow: bool)
    | I64(overflow: bool)
    | U128(overflow: bool)
    | I128(overflow: bool)
    | NativeArrayIndex
    | BigInt
    | Bool
    | Sequence
    | Map
    | NoRange
  {
    predicate CanOverflow() {
      (U8? || I8? || U16? || I16? || U32? || I32? || U64? || I64? || U128? || I128?) && overflow
    }
    predicate HasArithmeticOperations() {
      !Bool? && !Map? && !Sequence?
    }
  }

  datatype Attribute = Attribute(name: string, args: seq<string>)

  datatype NewtypeType = NewtypeType(baseType: Type, range: NewtypeRange, erase: bool)

  datatype TraitType =
    | ObjectTrait()     // Traits that extend objects with --type-system-refresh, all traits otherwise
    | GeneralTrait()  // Traits that don't necessarily extend objects with --type-system-refresh

  datatype TypeParameterInfo =
    TypeParameterInfo(variance: Variance, necessaryForEqualitySupportOfSurroundingInductiveDatatype: bool)

  datatype EqualitySupport = Never | ConsultTypeArguments

  datatype ResolvedTypeBase =
    | Class()
    | Datatype(equalitySupport: EqualitySupport, info: seq<TypeParameterInfo>)
    | Trait(traitType: TraitType)
    | SynonymType(baseType: Type)
    | Newtype(baseType: Type, range: NewtypeRange, erase: bool)

  datatype ResolvedType = ResolvedType(
    path: seq<Ident>,
    typeArgs: seq<Type>,
    kind: ResolvedTypeBase,
    attributes: seq<Attribute>,
    properMethods: seq<Name>,
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

  datatype Class = Class(
    name: Name,
    docString: string,
    enclosingModule: Ident,
    typeParams: seq<TypeArgDecl>,
    superTraitTypes: seq<Type>,
    fields: seq<Field>,
    body: seq<ClassItem>,
    attributes: seq<Attribute>)

  datatype Trait = Trait(
    name: Name,
    docString: string,
    typeParams: seq<TypeArgDecl>,
    traitType: TraitType,
    parents: seq<Type>,
    downcastableTraits: seq<Type>,
    body: seq<ClassItem>,
    attributes: seq<Attribute>)

  datatype Datatype = Datatype(
    name: Name,
    docString: string,
    enclosingModule: Ident,
    typeParams: seq<TypeArgDecl>,
    ctors: seq<DatatypeCtor>,
    body: seq<ClassItem>,
    isCo: bool,
    equalitySupport: EqualitySupport,
    attributes: seq<Attribute>,
    superTraitTypes: seq<Type>,
    superTraitNegativeTypes: seq<Type> // Traits that one or more superTraits know they can downcast to, but the datatype does not.
  )

  datatype DatatypeDtor = DatatypeDtor(
    formal: Formal,
    callName: Option<string>)

  datatype DatatypeCtor = DatatypeCtor(
    name: Name,
    docString: string,
    args: seq<DatatypeDtor>,
    hasAnyArgs: bool /* includes ghost */)

  datatype Newtype =
    Newtype(
      name: Name,
      docString: string,
      typeParams: seq<TypeArgDecl>, base: Type,
      range: NewtypeRange, constraint: Option<NewtypeConstraint>,
      witnessStmts: seq<Statement>, witnessExpr: Option<Expression>,
      equalitySupport: EqualitySupport,
      attributes: seq<Attribute>,
      classItems: seq<ClassItem>)

  datatype NewtypeConstraint = NewtypeConstraint(variable: Formal, constraintStmts: seq<Statement>)

  // At this point, constraints have been entirely removed,
  // but synonym types might have different witnesses to use for by the compiler
  datatype SynonymType = SynonymType(
    name: Name,
    docString: string,
    typeParams: seq<TypeArgDecl>,
    base: Type,
    witnessStmts: seq<Statement>,
    witnessExpr: Option<Expression>,
    attributes: seq<Attribute>)

  datatype ClassItem = Method(Method)

  datatype Field = Field(formal: Formal, isConstant: bool, defaultValue: Option<Expression>, isStatic: bool)

  datatype Formal = Formal(name: VarName, typ: Type, attributes: seq<Attribute>)

  datatype Method = Method(
    docString: string,
    attributes: seq<Attribute>,
    isStatic: bool,
    hasBody: bool,
    outVarsAreUninitFieldsToAssign: bool, // For constructors
    wasFunction: bool, // To choose between "&self" and "&mut self"
    overridingPath: Option<seq<Ident>>,
    name: Name,
    typeParams: seq<TypeArgDecl>,
    params: seq<Formal>,
    inheritedParams: seq<Formal>,
    body: seq<Statement>,
    outTypes: seq<Type>,
    outVars: Option<seq<VarName>>)

  datatype CallSignature = CallSignature(parameters: seq<Formal>, inheritedParams: seq<Formal>)

  datatype CallName =
    CallName(name: Name, onType: Option<Type>, receiverArg: Option<Formal>, receiverAsArgument: bool, signature: CallSignature) |
    MapBuilderAdd | MapBuilderBuild | SetBuilderAdd | SetBuilderBuild

  datatype Statement =
    DeclareVar(name: VarName, typ: Type, maybeValue: Option<Expression>) |
    Assign(lhs: AssignLhs, value: Expression) |
    If(cond: Expression, thn: seq<Statement>, els: seq<Statement>) |
    Labeled(lbl: string, body: seq<Statement>) |
    While(cond: Expression, body: seq<Statement>) |
    Foreach(boundName: VarName, boundType: Type, over: Expression, body: seq<Statement>) |
    Call(on: Expression, callName: CallName, typeArgs: seq<Type>, args: seq<Expression>, outs: Option<seq<VarName>>) |
    Return(expr: Expression) |
    EarlyReturn() |
    Break(toLabel: Option<string>) |
    TailRecursive(body: seq<Statement>) |
    JumpTailCallStart() |
    Halt() |
    Print(Expression) |
    ConstructorNewSeparator(fields: seq<Field>)
  {
  }

  datatype AssignLhs =
    Ident(ident: VarName) |
    Select(expr: Expression, field: VarName, isConstant: bool) |
    Index(expr: Expression, indices: seq<Expression>)

  datatype CollKind = Seq | Array | Map

  datatype TypedBinOp =
    TypedBinOp(op: BinOp, leftType: Type, rightType: Type, resultType: Type)

  datatype BinOp =
    Eq(referential: bool) |
    Div(overflow: bool) | EuclidianDiv() |
    Mod() | EuclidianMod() |
    Lt() | // a <= b is !(b < a)
    LtChar() |
    Plus(overflow: bool) | Minus(overflow: bool) | Times(overflow: bool) |
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

  datatype SelectContext =
    SelectContextDatatype | SelectContextGeneralTrait | SelectContextClassOrObjectTrait

  datatype Expression =
    Literal(Literal) |
    Ident(name: VarName) |
    Companion(seq<Ident>, typeArgs: seq<Type>) |
    ExternCompanion(seq<Ident>) |
    Tuple(seq<Expression>) |
    New(path: seq<Ident>, typeArgs: seq<Type>, args: seq<Expression>) |
    NewUninitArray(dims: seq<Expression>, typ: Type) |
    ArrayIndexToInt(value: Expression) |
    FinalizeNewArray(value: Expression, typ: Type) |
    DatatypeValue(datatypeType: ResolvedType, typeArgs: seq<Type>, variant: Name, isCo: bool, contents: seq<(VarName, Expression)>) |
    Convert(value: Expression, from: Type, typ: Type) |
    SeqConstruct(length: Expression, elem: Expression) |
    SeqValue(elements: seq<Expression>, typ: Type) |
    SetValue(elements: seq<Expression>) |
    MultisetValue(elements: seq<Expression>) |
    MapValue(mapElems: seq<(Expression, Expression)>, domainType: Type, rangeType: Type) |
    MapBuilder(keyType: Type, valueType: Type) |
    SeqUpdate(expr: Expression, indexExpr: Expression, value: Expression, collectionType: Type, exprType: Type) |
    MapUpdate(expr: Expression, indexExpr: Expression, value: Expression, collectionType: Type, exprType: Type) |
    SetBuilder(elemType: Type) |
    ToMultiset(Expression) |
    This() |
    Ite(cond: Expression, thn: Expression, els: Expression) |
    UnOp(unOp: UnaryOp, expr: Expression, format1: Format.UnaryOpFormat) |
    BinOp(op: TypedBinOp, left: Expression, right: Expression, format2: Format.BinaryOpFormat) |
    ArrayLen(expr: Expression, exprType: Type, dim: nat, native: bool) |
    MapKeys(expr: Expression) |
    MapValues(expr: Expression) |
    MapItems(expr: Expression) |
    Select(expr: Expression, field: VarName, fieldMutability: FieldMutability, selectContext: SelectContext, isfieldType: Type) |
    SelectFn(expr: Expression, field: VarName, onDatatype: bool, isStatic: bool, isConstant: bool, arguments: seq<Type>) |
    Index(expr: Expression, collKind: CollKind, indices: seq<Expression>) |
    IndexRange(expr: Expression, isArray: bool, low: Option<Expression>, high: Option<Expression>) |
    TupleSelect(expr: Expression, index: nat, fieldType: Type) |
    Call(on: Expression, callName: CallName, typeArgs: seq<Type>, args: seq<Expression>) |
    Lambda(params: seq<Formal>, retType: Type, body: seq<Statement>) |
    BetaRedex(values: seq<(Formal, Expression)>, retType: Type, expr: Expression) |
    IIFE(ident: VarName, typ: Type, value: Expression, iifeBody: Expression) |
    Apply(expr: Expression, args: seq<Expression>) |
    TypeTest(on: Expression, dType: seq<Ident>, variant: Name) |
    Is(expr: Expression, fromType: Type, toType: Type) |
    InitializationValue(typ: Type) |
    BoolBoundedPool() |
    SetBoundedPool(of: Expression) |
    MapBoundedPool(of: Expression) |
    SeqBoundedPool(of: Expression, includeDuplicates: bool) |
    MultisetBoundedPool(of: Expression, includeDuplicates: bool) |
    ExactBoundedPool(of: Expression) |
    IntRange(elemType: Type, lo: Expression, hi: Expression, up: bool) |
    UnboundedIntRange(start: Expression, up: bool) |
    Quantifier(elemType: Type, collection: Expression, is_forall: bool, lambda: Expression) {
    predicate IsThisUpcast() {
      Convert? && value.This? && from.Extends(typ)
    }
  }

  // Since constant fields need to be set up in the constructor,
  // accessing constant fields is done in two ways:
  // - The internal field access (through the internal field that contains the value of the constant)
  //   it's not initialized at the beginning of the constructor.
  // - The external field access (through a function), which when accessed
  //   must always be initialized.
  // For Select expressions, it's important to know how the field is being accessed
  // For mutable fields, there is no wrapping function so only one way to access the mutable field
  datatype FieldMutability =
    | ConstantField // Access a class constant field after initialization, or a datatype constant field
    | InternalClassConstantFieldOrDatatypeDestructor // Access a class internal field before initialization, or a datatype destructor
    | ClassMutableField
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
