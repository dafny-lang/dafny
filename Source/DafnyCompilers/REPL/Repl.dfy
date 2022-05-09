include "../Interp.dfy"
include "../CompilerCommon.dfy"
include "../Printer.dfy"
include "../Library.dfy"
include "../CSharpDafnyASTModel.dfy"
include "../CSharpDafnyInterop.dfy"
include "../../AutoExtern/CSharpModel.dfy"

import DafnyCompilerCommon.AST
import DafnyCompilerCommon.Translator
import opened Lib.Datatypes

module {:extern "REPL"} REPL {
  import System
  import C = CSharpDafnyASTModel

  class {:extern} {:compile false} ReplHelper {
    constructor {:extern} (input: System.String)

    var {:extern} Expression: C.Expression;

    static method {:extern} Setup()

    static method {:extern} Input()
      returns (e: System.String?)

    method {:extern} Parse()
      returns (b: bool)

    method {:extern} Resolve()
      returns (b: bool)
  }
}

datatype ReadError =
  EOF | MissingInput
{
  function method ToString() : string {
    match this {
      case EOF => "End of file"
      case MissingInput => "Missing input"
    }
  }
}

datatype REPLError =
  | ReadError(re: ReadError)
  | ParseError
  | ResolutionError
  | TranslationError(te: Translator.TranslationError)
  | InterpError(ie: Interp.InterpError)
  | Unsupported(e: AST.Expr)
{
  function method ToString() : string {
    match this
      case ReadError(re) =>
        "Read error: " + re.ToString()
      case ParseError() =>
        "Parse error"
      case ResolutionError() =>
        "Resolution error"
      case TranslationError(te) =>
        "Translation error: " + te.ToString()
      case InterpError(ie) =>
        "Execution error: " + ie.ToString()
      case Unsupported(ex) =>
        "Unsupported expression" // FIXME change checker to return the unsupported subexpression
  }
}


type REPLResult<+A> = Result<A, REPLError>

function method TranslateExpression(cExpr: CSharpDafnyASTModel.Expression) : REPLResult<AST.Expr>
  reads *
{
  Translator.TranslateExpression(cExpr).MapFailure(e => TranslationError(e))
}

method Read() returns (r: REPLResult<AST.Expr>)
  ensures r.Success? ==> Interp.SupportsInterp(r.value)
{
  var cStr := REPL.ReplHelper.Input();
  :- Need(cStr != null, ReadError(EOF));
  :- Need(CSharpDafnyInterop.TypeConv.AsString(cStr) != "", ReadError(MissingInput));
  var helper := new REPL.ReplHelper(cStr);
  var parseOk := helper.Parse();
  :- Need(parseOk, ParseError);
  var tcOk := helper.Resolve();
  :- Need(tcOk, ResolutionError);
  var expr :- TranslateExpression(helper.Expression);
  :- Need(Interp.SupportsInterp(expr), Unsupported(expr));
  return Success(expr);
}

method Eval(e: AST.Expr) returns (r: REPLResult<Values.T>)
  requires Interp.SupportsInterp(e)
  decreases *
{
  var fuel: nat := 1024;
  while true
    decreases *
  {
    match Interp.InterpExpr(e, fuel)
      case Success(Return(val, _)) => return Success(val);
      case Failure(OutOfFuel(_)) =>
        print "Trying again with fuel := ", fuel;
        fuel := fuel * 2;
      case Failure(err) =>
        return Failure(InterpError(err));
  }
}

method ReadEval() returns (r: REPLResult<Values.T>)
  decreases *
{
  var expr :- Read();
  var val :- Eval(expr);
  return Success(val);
}

method Main()
  decreases *
{
  // FIXME: Missing type check means `[true, "A", 3]` is accepted, and so is `[1 := 2]`
  REPL.ReplHelper.Setup();
  while true
    decreases *
  {
    print "dfy~ ";
    var r := ReadEval();
    match r {
      case Failure(ReadError(EOF)) =>
        return;
      case Failure(ReadError(MissingInput)) =>
        continue;
      case Failure(err) =>
        print err.ToString();
      case Success(val) =>
        print Interp.Printer.ToString(val);
    }
    print "\n";
  }
}
