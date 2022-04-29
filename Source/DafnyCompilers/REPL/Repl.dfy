include "../Semantics.dfy"
include "../CompilerCommon.dfy"
include "../Printer.dfy"
include "../Library.dfy"
include "../CSharpDafnyASTModel.dfy"

import C = CSharpDafnyASTModel
import D = DafnyCompilerCommon
import opened Lib.Datatypes

type Expr = D.AST.Expr.Expr

method {:extern "Read"} Read() returns (e: C.Expression)

function method Translate(cE: C.Expression) : (o: Option<Expr>)
  ensures o.Some? ==> Interp.SupportsInterp(o.t)
  reads *
{
  var e := D.Translator.TranslateExpression(cE);
  if Interp.SupportsInterp(e) then Some(e) else None
}

function method Eval(e: Expr) : Values.T
  requires Interp.SupportsInterp(e)
{
  Interp.InterpExpr(e).1
}

method Main()
  decreases *
{
  while true
    decreases *
  {
    var cExpr := Read();
    match Translate(cExpr)
      case None => print "Unsupported expression";
      case Some(e) =>
        var val := Eval(e);
        print Interp.Printer.ToString(val);
  }
}
