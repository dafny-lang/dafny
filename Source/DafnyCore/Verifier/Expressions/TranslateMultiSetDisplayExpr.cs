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
      var isLit = true;
      var boxedElements = new List<Expr>();
      foreach (Expression ee in displayExpr.Elements) {
        var rawElement = TrExpr(ee);
        isLit = isLit && BoogieGenerator.IsLit(rawElement);
        boxedElements.Add(BoxIfNecessary(GetToken(displayExpr), rawElement, Cce.NonNull(ee.Type)));
      }
      // Canonicalize element order so permuted displays produce identical terms. Unlike a set, a multiset is
      // multiplicity-sensitive, so repeated elements are kept (dropDuplicates: false).
      Expr result = BoogieGenerator.FunctionCall(GetToken(displayExpr), BuiltinFunction.MultiSetEmpty, Predef.BoxType);
      foreach (var boxedElement in CanonicalizeDisplayElements(boxedElements, dropDuplicates: false)) {
        result = BoogieGenerator.FunctionCall(GetToken(displayExpr), BuiltinFunction.MultiSetUnionOne, Predef.BoxType, result,
          boxedElement);
      }

      if (isLit) {
        // Lit-lifting: All elements are lit, so the multiset is Lit too
        result = MaybeLit(result, Predef.BoxType);
      }

      return result;
    }
  }
}