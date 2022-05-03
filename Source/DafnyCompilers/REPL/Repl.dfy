include "../Semantics.dfy"
include "../CompilerCommon.dfy"
include "../Printer.dfy"
include "../Library.dfy"
include "../CSharpDafnyASTModel.dfy"
include "../CSharpDafnyInterop.dfy"
include "../../AutoExtern/CSharpModel.dfy"

import C = CSharpDafnyASTModel
import DafnyCompilerCommon.AST
import opened Lib.Datatypes

method {:extern "ParseExpression"} ParseExpression(s: System.String)
  returns (e: C.Expression?)

method {:extern "Input"} Input()
  returns (e: System.String?)

datatype REPLError =
  | ReadError
  | ParseError
  | InterpError(ie: Interp.InterpError)

type REPLResult<+A> = Result<A, REPLError>

method Read() returns (r: REPLResult<AST.Expr>)
  ensures r.Success? ==> Interp.SupportsInterp(r.value)
{
  var cStr := Input();
  :- Need (cStr != null, ReadError);
  :- Need (CSharpDafnyInterop.TypeConv.AsString(cStr) != "", ReadError);
  var cExpr := ParseExpression(cStr);
  :- Need (cExpr != null, ParseError);
  var expr := DafnyCompilerCommon.Translator.TranslateExpression(cExpr);
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

method ReportError(err: REPLError) {
  match err
    case ReadError => // Ignore silently
    case ParseError => print "Parse error";
    case InterpError(ie: Interp.InterpError) =>
      print "Execution error: ";
      match ie
        case TypeError(e: Expr, value: V.T, expected: Type) => print "Type mismatch";
        case InvalidExpression(e: Expr) => print "Invalid expression";
        case Unsupported(e: Expr) => print "Unsupported expression";
        case Overflow(x: int, low: int, high: int) => print "Overflow";
        case DivisionByZero => print "Division by zero";
}

method Main()
  decreases *
{
  while true
    decreases *
  {
    print "∂~ ";
    var r := ReadEval();
    match r {
      case Failure(err) =>
        ReportError(err);
      case Success(val) =>
        print Interp.Printer.ToString(val);
    }
    print "\n";
  }
}
