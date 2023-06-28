
module {:extern "DAST"} DAST {

  datatype TopLevel = Module(Module) | Other(a: string, b: string)

  datatype Module = Module(name: string, body: seq<ModuleItem>)

  datatype ModuleItem = Module(Module) | Class(Class)

  datatype Class = Class(name: string, body: seq<ClassItem>)

  datatype ClassItem = Method(Method) | Other(a: string)

  datatype Method = Method(name: string, body: seq<Statement>)

  datatype Statement = Assign(name: string, value: Expression) | Print(Expression) | If(condition: Expression, body: seq<Statement>, elseBody: seq<Statement>)

  datatype Expression = Literal(Literal) | Other(a: string)

  datatype Literal = IntLiteral(int) | StringLiteral(string)
}
