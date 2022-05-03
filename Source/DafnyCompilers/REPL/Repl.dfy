include "../Interp.dfy"
include "../CompilerCommon.dfy"
include "../Printer.dfy"
include "../Library.dfy"
include "../CSharpDafnyASTModel.dfy"
include "../CSharpDafnyInterop.dfy"
include "../../AutoExtern/CSharpModel.dfy"

import DafnyCompilerCommon.AST
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

datatype ReadError = EOF | MissingInput

datatype REPLError =
  | ReadError(re: ReadError)
  | ParseError
  | ResolutionError
  | InterpError(ie: Interp.InterpError)

type REPLResult<+A> = Result<A, REPLError>

method Read() returns (r: REPLResult<AST.Expr>)
  ensures r.Success? ==> Interp.SupportsInterp(r.value)
{
  var cStr := REPL.ReplHelper.Input();
  :- Need (cStr != null, ReadError(EOF));
  :- Need (CSharpDafnyInterop.TypeConv.AsString(cStr) != "", ReadError(MissingInput));
  var helper := new REPL.ReplHelper(cStr);
  var parseOk := helper.Parse();
  :- Need (parseOk, ParseError);
  var tcOk := helper.Resolve();
  :- Need (tcOk, ResolutionError);
  var expr := DafnyCompilerCommon.Translator.TranslateExpression(helper.Expression);
  :- Need(Interp.SupportsInterp(expr), InterpError(Interp.Unsupported(expr)));
  return Success(expr);
}

function method Eval(e: AST.Expr) : REPLResult<Values.T>
  requires Interp.SupportsInterp(e)
{
  var OK(val, ctx) :- Interp.InterpExpr(e).MapFailure(e => InterpError(e)); // Map error
  Success(val)
}

method ReadEval() returns (r: REPLResult<Values.T>) {
  var expr :- Read();
  var val :- Eval(expr);
  return Success(val);
}

method ReportError(err: REPLError)
  requires !err.ReadError?
{
  match err
    case ParseError() => print "Parse error";
    case ResolutionError() => print "Resolution error";
    case InterpError(ie: Interp.InterpError) =>
      print "Execution error: ";
      match ie
        case TypeError(e: Expr, value: V.T, expected: Type) => print "Type mismatch";
        case InvalidExpression(e: Expr) => print "Invalid expression";
        case Unsupported(e: Expr) => print "Unsupported expression";
        case Overflow(x: int, low: int, high: int) => print "Overflow";
        case DivisionByZero() => print "Division by zero";
}

method Main()
  decreases *
{
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
        ReportError(err);
      case Success(val) =>
        print Interp.Printer.ToString(val);
    }
    print "\n";
  }
}
