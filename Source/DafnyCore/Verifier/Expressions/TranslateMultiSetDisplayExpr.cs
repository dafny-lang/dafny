namespace Microsoft.Dafny;

using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Numerics;
using Dafny;
using Microsoft.BaseTypes;
using Microsoft.Boogie;
using Bpl = Microsoft.Boogie;
using static Microsoft.Dafny.Util;

public partial class BoogieGenerator {
  public partial class ExpressionTranslator {

    private Expr TranslateMultiSetDisplayExpr(MultiSetDisplayExpr displayExpr) {
      Expr result = BoogieGenerator.FunctionCall(GetToken(displayExpr), BuiltinFunction.MultiSetEmpty, Predef.BoxType);
      var isLit = true;
      foreach (Expression ee in displayExpr.Elements) {
        var rawElement = TrExpr(ee);
        isLit = isLit && BoogieGenerator.IsLit(rawElement);
        var ss = BoxIfNecessary(GetToken(displayExpr), rawElement, Cce.NonNull(ee.Type));
        result = BoogieGenerator.FunctionCall(GetToken(displayExpr), BuiltinFunction.MultiSetUnionOne, Predef.BoxType, result,
          ss);
      }

      if (isLit) {
        // Lit-lifting: All elements are lit, so the multiset is Lit too
        result = MaybeLit(result, Predef.BoxType);
      }

      return result;
    }
  }
}