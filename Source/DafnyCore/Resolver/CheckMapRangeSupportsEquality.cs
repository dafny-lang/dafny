//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

namespace Microsoft.Dafny;

class CheckMapRangeSupportsEquality : ASTVisitor<IASTVisitorContext> {
  private readonly ErrorReporter reporter;

  public CheckMapRangeSupportsEquality(ErrorReporter reporter) {
    this.reporter = reporter;
  }

  public override IASTVisitorContext GetContext(IASTVisitorContext astVisitorContext, bool inFunctionPostcondition) {
    return astVisitorContext;
  }


  protected override bool VisitOneExpression(Expression expr, IASTVisitorContext context) {

    if (expr is ExprDotName) {
      var e = (ExprDotName)expr;
      if (e.Lhs.Type != null && e.Lhs.Type.IsMapType && (e.SuffixName == "Values" || e.SuffixName == "Items")) {
        if (!e.Lhs.Type.AsMapType.Range.SupportsEquality) {
          reporter.Error(MessageSource.Resolver, expr, "NO NO NO");
        }
      }
    }

    return base.VisitOneExpression(expr, context);
  }
}