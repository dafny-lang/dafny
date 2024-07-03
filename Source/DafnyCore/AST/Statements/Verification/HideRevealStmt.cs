using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public class HideRevealStmt : Statement, ICloneable<HideRevealStmt>, ICanFormat {
  public const string RevealLemmaPrefix = "reveal_";

  public readonly List<Expression> Exprs;
  [FilledInDuringResolution]
  public readonly List<AssertLabel> LabeledAsserts = new();  // to indicate that "Expr" denotes a labeled assertion
  [FilledInDuringResolution]
  public readonly List<Statement> ResolvedStatements = new();
  [FilledInDuringResolution] public List<MemberDecl> OffsetMembers = new();
  public HideRevealCmd.Modes Mode { get; private set; }
  public bool Wildcard { get; private set; }

  public override IEnumerable<Statement> SubStatements => ResolvedStatements;

  public override IEnumerable<Statement> PreResolveSubStatements => Enumerable.Empty<Statement>();

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Exprs != null);
    Contract.Invariant(LabeledAsserts.Count <= Exprs.Count);
  }

  public HideRevealStmt Clone(Cloner cloner) {
    return new HideRevealStmt(cloner, this);
  }

  public HideRevealStmt(Cloner cloner, HideRevealStmt original) : base(cloner, original) {
    Mode = original.Mode;
    Exprs = original.Exprs?.Select(cloner.CloneExpr).ToList();
    Wildcard = original.Wildcard;
    if (cloner.CloneResolvedFields) {
      OffsetMembers = original.OffsetMembers.ToList();
      LabeledAsserts = original.LabeledAsserts.Select(a => new AssertLabel(cloner.Tok(a.Tok), a.Name)).ToList();
      ResolvedStatements = original.ResolvedStatements.Select(stmt => cloner.CloneStmt(stmt, false)).ToList();
    }
  }

  public HideRevealStmt(RangeToken rangeToken, HideRevealCmd.Modes mode)
    : base(rangeToken) {
    Wildcard = true;
    this.Exprs = null;
    Mode = mode;
  }

  public HideRevealStmt(RangeToken rangeToken, List<Expression> exprs, HideRevealCmd.Modes mode)
    : base(rangeToken) {
    Contract.Requires(exprs != null);
    this.Exprs = exprs;
    Wildcard = false;
    Mode = mode;
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

  public void Resolve(PreTypeResolver resolver, ResolutionContext resolutionContext) {
    ((MethodOrFunction)resolutionContext.CodeContext).ContainsHide |= Mode == HideRevealCmd.Modes.Hide;

    if (Wildcard) {
      return;
    }

    foreach (var expr in Exprs) {
      var name = SingleName(expr);
      var labeledAssert = name == null ? null : resolver.DominatingStatementLabels.Find(name) as AssertLabel;
      if (labeledAssert != null) {
        LabeledAsserts.Add(labeledAssert);
      } else {
        if (expr is NameSegment or ExprDotName) {
          if (expr is NameSegment) {
            resolver.ResolveNameSegment((NameSegment)expr, true, null, resolutionContext, true);
          } else {
            resolver.ResolveDotSuffix((ExprDotName)expr, true, null, resolutionContext, true);
          }
          var callee = (MemberSelectExpr)((ConcreteSyntaxExpression)expr).ResolvedExpression;
          if (callee == null) {
            // error from resolving child
          } else {
            OffsetMembers.Add(callee.Member);
            if (callee.Member.IsOpaque && Mode == HideRevealCmd.Modes.Reveal) {
              var revealResolutionContext = resolutionContext with { InReveal = true };
              var exprClone = new Cloner().CloneExpr(expr);
              if (exprClone is NameSegment) {
                resolver.ResolveNameSegment((NameSegment)exprClone, true, null, revealResolutionContext, true);
              } else {
                resolver.ResolveDotSuffix((ExprDotName)exprClone, true, null, revealResolutionContext, true);
              }
              var call = new CallStmt(RangeToken, new List<Expression>(),
                ((MemberSelectExpr)((ConcreteSyntaxExpression)exprClone).ResolvedExpression),
                new List<ActualBinding>(), expr.tok);
              ResolvedStatements.Add(call);
            }
          }
        } else if (expr is ApplySuffix applySuffix) {
          var methodCallInfo = resolver.ResolveApplySuffix(applySuffix, resolutionContext, true);
          if (methodCallInfo == null) {
            // error has already been reported
          } else if (methodCallInfo.Callee.Member is TwoStateLemma && !resolutionContext.IsTwoState) {
            resolver.Reporter.Error(MessageSource.Resolver, methodCallInfo.Tok, "a two-state function can only be revealed in a two-state context");
          } else if (methodCallInfo.Callee.AtLabel != null) {
            Contract.Assert(methodCallInfo.Callee.Member is TwoStateLemma);
            resolver.Reporter.Error(MessageSource.Resolver, methodCallInfo.Tok, "to reveal a two-state function, do not list any parameters or @-labels");
          } else {
            var exprClone = (ApplySuffix)new Cloner().CloneExpr(applySuffix);
            var revealResolutionContext = resolutionContext with { InReveal = true };
            var revealMethodCallInfo = resolver.ResolveApplySuffix(exprClone, revealResolutionContext, true);
            if (revealMethodCallInfo.Callee.Member.IsOpaque && Mode == HideRevealCmd.Modes.Reveal) {
              var call = new CallStmt(RangeToken, new List<Expression>(), revealMethodCallInfo.Callee, revealMethodCallInfo.ActualParameters);
              ResolvedStatements.Add(call);
            }
          }
        } else {
          resolver.Reporter.Error(MessageSource.Resolver, Tok, "can't use parenthesis when revealing");
        }
      }
    }

    foreach (var a in ResolvedStatements) {
      resolver.ResolveStatement(a, resolutionContext);
    }
  }
}