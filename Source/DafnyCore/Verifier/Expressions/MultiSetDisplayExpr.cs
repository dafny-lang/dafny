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
      Bpl.Expr s = BoogieGenerator.FunctionCall(GetToken(displayExpr), BuiltinFunction.MultiSetEmpty, Predef.BoxType);
      var isLit = true;
      foreach (Expression ee in displayExpr.Elements) {
        var rawElement = TrExpr(ee);
        isLit = isLit && BoogieGenerator.IsLit(rawElement);
        Boogie.Expr ss = BoxIfNecessary(GetToken(displayExpr), rawElement, cce.NonNull(ee.Type));
        s = BoogieGenerator.FunctionCall(GetToken(displayExpr), BuiltinFunction.MultiSetUnionOne, Predef.BoxType, s,
          ss);
      }

      if (isLit) {
        // Lit-lifting: All elements are lit, so the multiset is Lit too
        s = MaybeLit(s, Predef.BoxType);
      }

      return s;
    }
  }
}