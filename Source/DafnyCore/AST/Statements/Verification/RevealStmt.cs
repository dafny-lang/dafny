using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class RevealStmt : Statement, ICloneable<RevealStmt>, ICanFormat {
  public const string RevealLemmaPrefix = "reveal_";

  public readonly List<Expression> Exprs;
  [FilledInDuringResolution] public readonly List<AssertLabel> LabeledAsserts = new List<AssertLabel>();  // to indicate that "Expr" denotes a labeled assertion
  [FilledInDuringResolution] public readonly List<Statement> ResolvedStatements = new List<Statement>();

  public override IEnumerable<Statement> SubStatements {
    get { return ResolvedStatements; }
  }

  public override IEnumerable<Statement> PreResolveSubStatements => Enumerable.Empty<Statement>();

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Exprs != null);
    Contract.Invariant(LabeledAsserts.Count <= Exprs.Count);
  }

  public RevealStmt Clone(Cloner cloner) {
    return new RevealStmt(cloner, this);
  }

  public RevealStmt(Cloner cloner, RevealStmt original) : base(cloner, original) {
    Exprs = original.Exprs.Select(cloner.CloneExpr).ToList();
    if (cloner.CloneResolvedFields) {
      LabeledAsserts = original.LabeledAsserts.Select(a => new AssertLabel(cloner.Tok(a.Tok), a.Name)).ToList();
      ResolvedStatements = original.ResolvedStatements.Select(stmt => cloner.CloneStmt(stmt, false)).ToList();
    }
  }

  public RevealStmt(RangeToken rangeToken, List<Expression> exprs)
    : base(rangeToken) {
    Contract.Requires(exprs != null);
    this.Exprs = exprs;
  }

  public static string SingleName(Expression e) {
    Contract.Requires(e != null);
    if (e is NameSegment || e is LiteralExpr) {
      return e.tok.val;
    } else {
      return null;
    }
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    return formatter.SetIndentPrintRevealStmt(indentBefore, OwnedTokens);
  }

  public void ResolveRevealStmt(PreTypeResolver preTypeResolver, ResolutionContext resolutionContext) {
    foreach (var expr in Exprs) {
      var name = RevealStmt.SingleName(expr);
      var labeledAssert = name == null ? null : preTypeResolver.DominatingStatementLabels.Find(name) as AssertLabel;
      if (labeledAssert != null) {
        LabeledAsserts.Add(labeledAssert);
      } else {
        var revealResolutionContext = resolutionContext with { InReveal = true };
        if (expr is ApplySuffix applySuffix) {
          var methodCallInfo = preTypeResolver.ResolveApplySuffix(applySuffix, revealResolutionContext, true);
          if (methodCallInfo == null) {
            // error has already been reported
          } else if (methodCallInfo.Callee.Member is TwoStateLemma && !revealResolutionContext.IsTwoState) {
            preTypeResolver.ReportError(methodCallInfo.Tok, "a two-state function can only be revealed in a two-state context");
          } else if (methodCallInfo.Callee.AtLabel != null) {
            Contract.Assert(methodCallInfo.Callee.Member is TwoStateLemma);
            preTypeResolver.ReportError(methodCallInfo.Tok, "to reveal a two-state function, do not list any parameters or @-labels");
          } else {
            var call = new CallStmt(RangeToken, new List<Expression>(), methodCallInfo.Callee, methodCallInfo.ActualParameters);
            ResolvedStatements.Add(call);
          }
        } else if (expr is NameSegment or ExprDotName) {
          if (expr is NameSegment) {
            preTypeResolver.ResolveNameSegment((NameSegment)expr, true, null, revealResolutionContext, true);
          } else {
            preTypeResolver.ResolveDotSuffix((ExprDotName)expr, true, null, revealResolutionContext, true);
          }
          var callee = (MemberSelectExpr)((ConcreteSyntaxExpression)expr).ResolvedExpression;
          if (callee == null) {
          } else if (callee.Member is Lemma or TwoStateLemma && Attributes.Contains(callee.Member.Attributes, "axiom")) {
            //The revealed member is a function
            preTypeResolver.ReportError(callee.tok, "to reveal a function ({0}), append parentheses", callee.Member.ToString().Substring(7));
          } else {
            var call = new CallStmt(RangeToken, new List<Expression>(), callee, new List<ActualBinding>(), expr.tok);
            ResolvedStatements.Add(call);
          }
        } else {
          preTypeResolver.ResolveExpression(expr, revealResolutionContext);
        }
      }
    }

    foreach (var a in ResolvedStatements) {
      preTypeResolver.ResolveStatement(a, resolutionContext);
    }
  }
}