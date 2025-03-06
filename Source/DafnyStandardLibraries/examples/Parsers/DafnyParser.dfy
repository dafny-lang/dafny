// A parser that can self-parse
module ExampleParsers.DafnyParser {
  import opened Std.Parsers.StringBuilders

  type Option<A> = StringBuilders.P.Option<A>

  datatype Program =
    Program(includes: seq<string>, declarations: seq<Declaration>)

  datatype Declaration =
    | Module(moduleName: Type, declarations: seq<Declaration>)
    | Import(opend: bool, imported: Type)
    | Datatype(datatypeName: Type, constructors: seq<Constructor>)
    | Const(name: string, tpe: Option<Type>, constDef: Expr)
    | TypeSynonymDecl(typeName: Type, typeArgs: seq<string>, typeDef: Type)

  datatype Constructor =
    Constructor(name: string, formals: seq<Formal>)

  datatype Formal =
    Formal(name: Option<string>, tpe: Type)

  datatype Type =
    | TypeName(name: string)
    | ApplyType(underlying: Type, args: seq<Type>)
    | SelectType(prefix: Type, field: Type)
  {
    function applyPrefix(name: string): Type {
      match this {
        case ApplyType(underlying, args) => ApplyType(underlying.applyPrefix(name), args)
        case SelectType(enclosing, field) => SelectType(enclosing.applyPrefix(name), field)
        case _ => SelectType(TypeName(name), this)
      }
    }
  }

  datatype Expr =
    | TODO

  const stringLit :=
    S("\"").e_I(Except("\"")).I_e(S("\""))

  /*const parserImport := S("import").e_I(WS()).e_I(
      S("opened").e_I(WS()).Maybe()).I_I(stringLit).M(
        (s: (Option<string>, string)) => Import(s.0.Some?, s.1));*/
  const parseInclude := WS().e_I(S("include")).??().e_I(WS()).e_I(stringLit)

  const parseIdentifier := CharTest((c: char) => c in "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_?$", "Identifier character")
                           .OneOrMore()

  const parseType: B<Type> :=
    Rec<Type>(
      (rec: B<Type>) =>
        parseIdentifier.Bind(
          (id: string) =>
            var init := TypeName(id);
            O([WS().e_I(S("<")).??().e_I(
                 rec.Bind((t: Type) =>
                            WS().e_I(S(",")).??().e_I(rec).ZeroOrMore()
                 ).I_e(WS().I_e(S(">"))).M((types: seq<Type>) =>
                                             ApplyType(TypeName(id), types)
                 )),
               WS().e_I(S(".")).??().e_I(rec).M(
                 (tpe: Type) =>
                   tpe.applyPrefix(id)
               ),
               Ok(init)
              ])
        ))

  const parseConstructor: B<Constructor> := Fail("parseConstructor not implemented yet")

  const parseDeclaration: B<Declaration> :=
    Rec(
      (declParser: B<Declaration>) =>
        O([
            WS().e_I(S("module")).??().e_I(WS()).e_I(parseType).I_e(WS()).I_e(S("{")).
            I_I(declParser.ZeroOrMore()).I_e(WS()).I_e(S("}")).M((r: (Type, seq<Declaration>)) =>
                                                                   Module(r.0, r.1)),
            WS().e_I(S("import")).??().e_I(WS()).e_I(S("opened").e_I(WS()).?()).I_I(parseType).M(
              (s: (Option<string>, Type)) => Import(s.0.Some?, s.1)),
            WS().e_I(S("datatype")).??().e_I(WS()).e_I(parseType).I_e(WS().e_I(S("="))).I_I(
              parseConstructor.OneOrMore()).M((r: (Type, seq<Constructor>)) =>
                                              Datatype(r.0, r.1)
            )
          ]))

  const parseProgram :=
    parseInclude.ZeroOrMore().I_I(parseDeclaration.ZeroOrMore()).M(
      (idecls: (seq<string>, seq<Declaration>)) =>
        Program(idecls.0, idecls.1))

  method {:test} TestParser() {
    var program := @"
include ""file""

import opened test

module Test {
  module Inner {
  
  }
}
";
    expect parseProgram.apply(program)
        == P.Success(
             Program.Program(
               ["file"],
               [Declaration.Import(true, Type.TypeName("test")), Declaration.Module(Type.TypeName("Test"), [Declaration.Module(Type.TypeName("Inner"), [])])]), "\n");
  }
}