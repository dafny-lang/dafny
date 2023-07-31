module {:extern "DAST"} DAST {
  datatype Module = Module(name: string, body: seq<ModuleItem>)

  datatype ModuleItem = Module(Module) | Class(Class) | Newtype(Newtype) | Datatype(Datatype)

  datatype Newtype = Newtype(name: string, base: Type)

  datatype Type = Path(seq<Ident>, typeArgs: seq<Type>, resolved: ResolvedType) | Tuple(seq<Type>) | Primitive(Primitive) | Passthrough(string) | TypeArg(Ident)

  datatype Primitive = String | Bool

  datatype ResolvedType = Datatype(path: seq<Ident>) | Newtype

  datatype Ident = Ident(id: string)

  datatype Class = Class(name: string, body: seq<ClassItem>)

  datatype Datatype = Datatype(name: string, enclosingModule: Ident, typeParams: seq<Type>, ctors: seq<DatatypeCtor>, body: seq<ClassItem>)

  datatype DatatypeCtor = DatatypeCtor(name: string, args: seq<Formal>, hasAnyArgs: bool /* includes ghost */)

  datatype ClassItem = Method(Method) | Field(Formal)

  datatype Formal = Formal(name: string, typ: Type)

  datatype Method = Method(isStatic: bool, name: string, typeParams: seq<Type>, params: seq<Formal>, body: seq<Statement>, outTypes: seq<Type>, outVars: Optional<seq<Ident>>)

  datatype Optional<T> = Some(T) | None

  datatype Statement =
    DeclareVar(name: string, typ: Type, maybeValue: Optional<Expression>) |
    Assign(name: string, value: Expression) |
    If(cond: Expression, thn: seq<Statement>, els: seq<Statement>) |
    Call(on: Expression, name: string, typeArgs: seq<Type>, args: seq<Expression>, outs: Optional<seq<Ident>>) |
    Return(expr: Expression) |
    EarlyReturn() |
    Print(Expression)

  datatype Expression =
    Literal(Literal) |
    Ident(string) |
    Companion(seq<Ident>) |
    Tuple(seq<Expression>) |
    DatatypeValue(path: seq<Ident>, variant: string, contents: seq<(string, Expression)>) |
    BinOp(op: string, left: Expression, right: Expression) |
    Select(expr: Expression, field: string, onDatatype: bool) |
    TupleSelect(expr: Expression, index: nat) |
    Call(on: Expression, name: string, typeArgs: seq<Type>, args: seq<Expression>) |
    TypeTest(on: Expression, dType: seq<Ident>, variant: string) |
    InitializationValue(typ: Type)

  datatype Literal = BoolLiteral(bool) | IntLiteral(int) | DecLiteral(string) | StringLiteral(string)
}
