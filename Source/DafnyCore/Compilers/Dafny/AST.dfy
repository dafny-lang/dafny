
module {:extern "DAST"} DAST {

  datatype TopLevel = Module(Module) | Other(a: string, b: string)

  datatype Module = Module(name: string, body: seq<ModuleItem>)

  datatype ModuleItem = Module(Module) | Class(Class) | Newtype(Newtype)

  datatype Newtype = Newtype(name: string, base: Type)

  datatype Type = Ident(Ident) | Other(a: string)

  datatype Ident = Ident(string)

  datatype Class = Class(name: string, body: seq<ClassItem>)

  datatype ClassItem = Method(Method) | Other(a: string)

  datatype Method = Method(name: string, body: seq<Statement>)

  datatype Statement = DeclareVar(name: string, typ: Type, value: Expression) | Assign(name: string, value: Expression) | Call(name: string, args: seq<Expression>) | Print(Expression)

  datatype Expression = Literal(Literal) | Ident(string) | DatatypeValue(contents: seq<Expression>) | BinOp(op: string, left: Expression, right: Expression)

  datatype Literal = IntLiteral(int) | DecLiteral(string) | StringLiteral(string)
}
