//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

namespace Microsoft.Dafny;

/// <summary>
/// This checker ensures that if the set of values or the set of items
/// of a map is used, then its range type supports equality.
/// </summary>
class CheckMapRangeSupportsEquality : ASTVisitor<IASTVisitorContext> {
  private readonly ErrorReporter reporter;

  public CheckMapRangeSupportsEquality(ErrorReporter reporter) {
    this.reporter = reporter;
  }

  public override IASTVisitorContext GetContext(IASTVisitorContext astVisitorContext, bool inFunctionPostcondition) {
    return astVisitorContext;
  }

  protected override bool VisitOneExpression(Expression expr, IASTVisitorContext context) {

    if (context is MemberDecl) {
      var member = (MemberDecl)context;
      if (member.IsGhost) {
        return base.VisitOneExpression(expr, context);
      }
    }

    if (expr is ExprDotName) {
      var e = (ExprDotName)expr;
      // Condition 1: the left-hand side is not a module and has a type
      // Condition 2: the left-hand side is a map
      // Condition 3: the expression produces a set that contains values from the range
      if (e.Lhs.Type != null && e.Lhs.Type.IsMapType && (e.SuffixName == "Values" || e.SuffixName == "Items")) {
        // The type of the range must support equality
        if (!e.Lhs.Type.AsMapType.Range.SupportsEquality) {
          reporter.Error(MessageSource.Resolver, expr,
            $"Cannot compute the set of {e.SuffixName} because the type of the range of the map ({e.Lhs.Type.AsMapType.Range}) does not support equality.");
        }
      }
    }
    return base.VisitOneExpression(expr, context);
  }
}