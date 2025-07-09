#nullable enable
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public class HideRevealStmt : Statement, ICloneable<HideRevealStmt>, ICanFormat, ICanResolveNewAndOld {
  public const string RevealLemmaPrefix = "reveal_";

  public string Kind => Mode == HideRevealCmd.Modes.Hide ? "hide" : "reveal";
  public string KindVerb => Mode == HideRevealCmd.Modes.Hide ? "hidden" : "revealed";
  public List<Expression>? Exprs;
  [FilledInDuringResolution]
  public List<AssertLabel> LabeledAsserts = [];  // to indicate that "Expr" denotes a labeled assertion
  [FilledInDuringResolution]
  public List<Statement> ResolvedStatements = [];
  [FilledInDuringResolution] public List<MemberDecl> OffsetMembers = [];
  public HideRevealCmd.Modes Mode { get; private set; }
  public bool Wildcard { get; private set; }

  public override IEnumerable<Statement> SubStatements => ResolvedStatements;

  public override IEnumerable<Statement> PreResolveSubStatements => [];

  [ContractInvariantMethod]
  void ObjectInvariant() {
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
      LabeledAsserts = original.LabeledAsserts.Select(a => new AssertLabel(cloner.Origin(a.Tok), a.Name)).ToList();
      ResolvedStatements = original.ResolvedStatements.Select(stmt => cloner.CloneStmt(stmt, false)).ToList();
    }
  }

  public HideRevealStmt(IOrigin origin, HideRevealCmd.Modes mode)
    : base(origin) {
    Wildcard = true;
    this.Exprs = null;
    Mode = mode;
  }

  [SyntaxConstructor]
  public HideRevealStmt(IOrigin origin, List<Expression>? exprs, HideRevealCmd.Modes mode, Attributes? attributes = null)
    : base(origin, attributes) {
    this.Exprs = exprs;
    Wildcard = exprs == null;
    Mode = mode;
  }

  public static string? SingleName(Expression e) {
    Contract.Requires(e != null);
    if (e is NameSegment || e is LiteralExpr) {
      return e.Origin.val;
    } else {
      return null;
    }
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    return formatter.SetIndentPrintRevealStmt(indentBefore, OwnedTokens);
  }

  public override void GenResolve(INewOrOldResolver resolver, ResolutionContext resolutionContext) {
    resolutionContext.CodeContext.ContainsHide |= Mode == HideRevealCmd.Modes.Hide;

    if (Wildcard) {
      return;
    }

    foreach (var expr in Exprs!) {
      var name = SingleName(expr);
      var labeledAssert = name == null ? null : resolver.DominatingStatementLabels.Find(name) as AssertLabel;
      if (labeledAssert != null) {
        LabeledAsserts.Add(labeledAssert);
      } else {
        Expression effectiveExpr = expr;
        if (expr is ApplySuffix applySuffix) {
          if (applySuffix.AtTok != null) {
            resolver.Reporter.Error(MessageSource.Resolver, expr.Origin, $"an @-label can not be used in a hide or reveal statement");
          }
          effectiveExpr = applySuffix.Lhs;
        }
        if (effectiveExpr is NameSegment or ExprDotName) {
          if (effectiveExpr is NameSegment segment) {
            resolver.ResolveNameSegment(segment, true, null, resolutionContext, true);
          } else {
            resolver.ResolveDotSuffix((ExprDotName)effectiveExpr, true, true, null, resolutionContext, true);
          }

          if (effectiveExpr.Resolved == null) {
            // error from resolving child
          } else if (effectiveExpr.Resolved is not MemberSelectExpr callee) {
            resolver.Reporter.Error(MessageSource.Resolver, effectiveExpr.Origin,
              $"cannot reveal '{name}' because no revealable constant, function, assert label, or requires label in the current scope is named '{name}'");
          } else {
            if (callee.Member is Function or ConstantField) {
              OffsetMembers.Add(callee.Member);
              if (!BoogieGenerator.IsOpaque(callee.Member, resolver.Options) || Mode != HideRevealCmd.Modes.Reveal) {
                continue;
              }

              var revealResolutionContext = resolutionContext with { InReveal = true };
              var exprClone = new Cloner().CloneExpr(effectiveExpr);
              if (exprClone is NameSegment nameSegment) {
                resolver.ResolveNameSegment(nameSegment, true, null, revealResolutionContext, true);
              } else {
                resolver.ResolveDotSuffix((ExprDotName)exprClone, true, true, null, revealResolutionContext, true);
              }

              var revealCallee = ((MemberSelectExpr)((ConcreteSyntaxExpression)exprClone).ResolvedExpression);
              if (revealCallee != null) {
                var call = new CallStmt(Origin, [],
                  revealCallee,
                  (List<Expression>)[], effectiveExpr.ReportingRange);
                ResolvedStatements.Add(call);
              }
            } else {
              resolver.Reporter.Error(MessageSource.Resolver, effectiveExpr.Origin,
                $"only functions and constants can be {KindVerb}");
            }
          }
        } else {
          resolver.Reporter.Error(MessageSource.Resolver, Origin, "can't use parenthesis when hiding or revealing");
        }
      }
    }

    foreach (var a in ResolvedStatements) {
      resolver.ResolveStatement(a, resolutionContext);
    }
  }

  public override void ResolveGhostness(ModuleResolver resolver, ErrorReporter reporter, bool mustBeErasable,
    ICodeContext codeContext,
    string? proofContext, bool allowAssumptionVariables, bool inConstructorInitializationPhase) {
    ResolvedStatements.ForEach(ss => ss.ResolveGhostness(resolver, reporter, true, codeContext,
      $"a {Kind} statement", allowAssumptionVariables, inConstructorInitializationPhase));
    IsGhost = ResolvedStatements.All(ss => ss.IsGhost);
  }
}