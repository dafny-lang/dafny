/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

/** A parser that can be used to parse Dafny programs. For now, it supports a few things:
    - Includes
    - Imports (possibly opened)
    - (Recursive)module declarations
*/

module ExampleParsers.DafnyModuleParser {
  import opened Std.Parsers.StringBuilders

  type Option<A> = StringBuilders.P.Option<A>

  datatype Program =
    Program(includes: seq<string>, declarations: seq<Declaration>)

  datatype Declaration =
    | Module(moduleName: string, declarations: seq<Declaration>)
    | Import(opend: bool, imported: string)

  const stringLit :=
    S("\"").e_I(Except("\"")).I_e(S("\""))

  const parseInclude := WS.e_I(S("include")).??().e_I(WS).e_I(stringLit)

  const canStartIdentifierChar := "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"

  const parseIdentifier: B<string> :=
    CharTest((c: char) => c in canStartIdentifierChar, "[" + canStartIdentifierChar + "]").Then((c: char) =>
                                                                                                  CharTest((c: char) => c in canStartIdentifierChar || c in "_?$", "Identifier character")
                                                                                                  .Rep().M((s: string) => [c] + s))

  const parseDeclaration: B<Declaration> :=
    Rec(
      (declParser: B<Declaration>) =>
        O([
            S("module").e_I(WS).e_I(parseIdentifier).I_e(WS).I_e(S("{")).I_e(WS).
            I_I(declParser.Rep()).I_e(WS).I_e(S("}")).I_e(WS)
            .M((r: (string, seq<Declaration>)) =>  Module(r.0, r.1)),
            S("import").e_I(WS).e_I(S("opened").e_I(WS).?()).I_I(parseIdentifier).M(
              (s: (Option<string>, string)) => Import(s.0.Some?, s.1))
          ]))

  const parseProgram :=
    parseInclude.Rep().I_e(WS).I_I(parseDeclaration.RepSep(WS)).M(
      (idecls: (seq<string>, seq<Declaration>)) =>
        Program(idecls.0, idecls.1)).I_e(WS).I_e(O([EOS, parseDeclaration.M(result => ())]))

  method ExpectFailure(program: string, result: ParseResult<Program>, message: string) {
    expect result.IsFailure();
    expect FailureToString(program, result)
        == message;
  }

  @Test
  @IsolateAssertions
  method TestParser() {
    var program := @"
include ""file""

import opened test

module Test {
  module Inner {
  
  }
}
";
    assert 0 <= 1 && 1 <= |program|;
    var inputFinal := ToInputEnd(program); // Inlining this fails
    var result := Apply(parseProgram, program);
    expect result
        == ParseResult.ParseSuccess(
             Program.Program(
               ["file"],
               [Declaration.Import(true, "test"),
                Declaration.Module(
                  "Test",
                  [
                    Declaration.Module("Inner", [])])]),
             inputFinal);
    program := "\nclass A {\n}\n";
    result := Apply(parseProgram, program);
    expect result.IsFailure();
    ExpectFailure(
      program,
      result,
      "Error:"      + "\n" +
      "2: class A {" + "\n" +
      "   ^"         + "\n" +
      "expected end of string, or" + "\n" +
      "expected 'module', or" + "\n" +
      "expected 'import'" + "\n");
  }
}