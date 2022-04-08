include "../CSharpDafnyASTModel.dfy"
include "../CSharpInterop.dfy"

// import opened CSharpSystem

module Utils {
  function method SeqMap<T, Q>(f: T ~> Q, ts: seq<T>) : seq<Q>
    reads * // FIXME
    requires forall t | t in ts :: f.requires(t)
  {
    if ts == [] then [] else [f(ts[0])] + SeqMap(f, ts[1..])
  }
}

module {:extern "DafnyInDafny.CSharp"} CSharpDafnyCompiler {
  import System
  import CSharpDafnyASTModel
  import opened CSharpInterop
  import opened CSharpDafnyInterop
  import opened Microsoft.Dafny
  import Utils

  module AST {
    datatype Expression =
      | StringLiteralExpr(str: string)
      | InvalidExpression

    datatype Stmt =
      | PrintStmt(stmts: seq<Expression>)
      | InvalidStmt

    type BlockStmt = seq<Stmt>

    datatype Method = Method(methodBody: BlockStmt)

    datatype Program = Program(mainMethod: Method)
  }

  module Translator {
    import AST
    import Utils
    import opened CSharpInterop
    import opened CSharpDafnyInterop
    import C = CSharpDafnyASTModel

    function method TranslateExpression(s: C.Expression) : AST.Expression reads * {
      if s is C.StringLiteralExpr then
        var p := s as C.StringLiteralExpr;
        if p.Value is System.String then
          AST.StringLiteralExpr(StringUtils.OfCString(p.Value as System.String))
        else
          AST.InvalidExpression
      else AST.InvalidExpression
    }

    function method TranslateStatement(s: C.Statement) : AST.Stmt reads * {
      if s is C.PrintStmt then
        var p := s as C.PrintStmt;
        AST.PrintStmt(Utils.SeqMap(TranslateExpression, ListUtils.ToSeq(p.Args)))
      else AST.InvalidStmt
    }

    function method TranslateBlock(b: C.BlockStmt) : AST.BlockStmt reads * {
      Utils.SeqMap(TranslateStatement, ListUtils.ToSeq(b.Body))
    }

    function method TranslateMethod(m: C.Method) : AST.Method reads * {
      AST.Method(TranslateBlock(m.Body))
    }

    function method TranslateProgram(p: C.Program) : AST.Program reads * {
      AST.Program(TranslateMethod(p.MainMethod))
    }
  }

  module Compiler {
    import opened AST

    class CSharpAST {}

    function method CompileExpression(s: Expression) : CSharpAST? {
      match s {
        case StringLiteralExpr(str) => null
        case InvalidExpression => null
      }
    }

    function method CompileStmt(s: Stmt) : CSharpAST? {
      match s {
        case PrintStmt(stmts) => null
        case InvalidStmt => null
      }
    }

    function method CompileMethod(m: Method) : CSharpAST? {
      match m {
        case Method(methodBody) => null
      }
    }

    function method CompileProgram(p: Program) : CSharpAST? {
      match p {
        case Program(mainMethod) => CompileMethod(mainMethod)
      }
    }
  }

  method WriteStr(output: ConcreteSyntaxTree, str: string) {
    output.Write(StringUtils.ToCString(str));
  }

  class {:extern} DafnyCSharpCompiler {
    constructor() {
    }

    method Compile(dafnyProgram: CSharpDafnyASTModel.Program,
                   output: ConcreteSyntaxTree) {
      WriteStr(output, "Console.WriteLine(\"Hello, world!\")");
    }

    method EmitCallToMain(mainMethod: CSharpDafnyASTModel.Method,
                          baseName: System.String,
                          output: ConcreteSyntaxTree) {
    }
  }
}
