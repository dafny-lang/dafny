
module {:extern "DAST"} DAST {

  datatype TopLevel = Module(Module) | Other(a: string, b: string)

  datatype Module = Module(name: string, body: seq<ModuleItem>)

  datatype ModuleItem = Module(Module) | Class(Class) | Newtype(Newtype)

  datatype Newtype = Newtype(name: string, base: Type)

  datatype Type = Ident(Ident) | Other(a: string)

  datatype Ident = Ident(string)

  datatype Class = Class(name: string, body: seq<ClassItem>)

  datatype ClassItem = Method(Method) | Other(a: string)

  datatype Method = Method(name: string, typeArgs: seq<Type>, body: seq<Statement>)

  datatype Optional<T> = Some(T) | None

  datatype Statement = DeclareVar(name: string, typ: Type, maybeValue: Optional<Expression>) | Assign(name: string, value: Expression) | Call(name: string, args: seq<Expression>) | Print(Expression) | Todo(reason: string)

  datatype Expression = Literal(Literal) | Ident(string) | DatatypeValue(contents: seq<Expression>) | BinOp(op: string, left: Expression, right: Expression) | Todo(reason: string)

  datatype Literal = IntLiteral(int) | DecLiteral(string) | StringLiteral(string)
}
