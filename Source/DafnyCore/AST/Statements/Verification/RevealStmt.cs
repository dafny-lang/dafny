using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class RevealStmt : Statement, ICloneable<RevealStmt>, ICanFormat {
  public const string RevealLemmaPrefix = "reveal_";

  public readonly List<Expression> Exprs;
  [FilledInDuringResolution] 
  public readonly List<AssertLabel> LabeledAsserts = new();  // to indicate that "Expr" denotes a labeled assertion
  [FilledInDuringResolution] 
  public readonly List<Statement> ResolvedStatements = new();
  [FilledInDuringResolution] public bool InBlindContext { get; private set; }
  [FilledInDuringResolution] public List<MemberDecl> RevealedMembers = new();
  

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

  public void Resolve(PreTypeResolver resolver, ResolutionContext resolutionContext)
  {
    foreach (var expr in Exprs) {
      var name = SingleName(expr);
      var labeledAssert = name == null ? null : resolver.DominatingStatementLabels.Find(name) as AssertLabel;
      if (labeledAssert != null) {
        LabeledAsserts.Add(labeledAssert);
      } else {
        if (resolutionContext.InBlindMethod) {
          InBlindContext = true;
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
              RevealedMembers.Add(callee.Member);
            }
          } else {
            resolver.Reporter.Error(MessageSource.Resolver, Tok, "can't use parenthesis when revealing");
          }
        } else {
          var revealResolutionContext = resolutionContext with { InReveal = true };
          if (expr is ApplySuffix applySuffix) {
            var methodCallInfo = resolver.ResolveApplySuffix(applySuffix, revealResolutionContext, true);
            if (methodCallInfo == null) {
              // error has already been reported
            } else if (methodCallInfo.Callee.Member is TwoStateLemma && !revealResolutionContext.IsTwoState) {
              resolver.Reporter.Error(MessageSource.Resolver, methodCallInfo.Tok, "a two-state function can only be revealed in a two-state context");
            } else if (methodCallInfo.Callee.AtLabel != null) {
              Contract.Assert(methodCallInfo.Callee.Member is TwoStateLemma);
              resolver.Reporter.Error(MessageSource.Resolver, methodCallInfo.Tok, "to reveal a two-state function, do not list any parameters or @-labels");
            } else {
              var call = new CallStmt(RangeToken, new List<Expression>(), methodCallInfo.Callee, methodCallInfo.ActualParameters);
              ResolvedStatements.Add(call);
            }
          } else if (expr is NameSegment or ExprDotName) {
            if (expr is NameSegment) {
              resolver.ResolveNameSegment((NameSegment)expr, true, null, revealResolutionContext, true);
            } else {
              resolver.ResolveDotSuffix((ExprDotName)expr, true, null, revealResolutionContext, true);
            }
            var callee = (MemberSelectExpr)((ConcreteSyntaxExpression)expr).ResolvedExpression;
            if (callee == null) {
            } else if (callee.Member is Lemma or TwoStateLemma && Attributes.Contains(callee.Member.Attributes, "axiom")) {
              //The revealed member is a function
              resolver.ReportError(callee.tok, "to reveal a function ({0}), append parentheses", callee.Member.ToString().Substring(7));
            } else {
              // TODO what is this case about? Revealing a constant?
              var call = new CallStmt(RangeToken, new List<Expression>(), callee, new List<ActualBinding>(), expr.tok);
              ResolvedStatements.Add(call);
            }
          } else {
            resolver.ResolveExpression(expr, revealResolutionContext);
          } 
        }
      }
    }

    foreach (var a in ResolvedStatements) {
      resolver.ResolveStatement(a, resolutionContext);
    }
  }
}