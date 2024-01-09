using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public abstract class PredicateStmt : Statement, ICanResolve {
  public readonly Expression Expr;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Expr != null);
  }

  protected PredicateStmt(Cloner cloner, PredicateStmt original) : base(cloner, original) {
    Expr = cloner.CloneExpr(original.Expr);
  }

  protected PredicateStmt(RangeToken rangeToken, Expression expr, Attributes attrs)
    : base(rangeToken, attrs) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(expr != null);
    this.Expr = expr;
  }

  protected PredicateStmt(RangeToken rangeToken, Expression expr)
    : this(rangeToken, expr, null) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(expr != null);
    this.Expr = expr;
  }

  public override void Resolve(ModuleResolver resolver, ResolutionContext context) {
    base.Resolve(resolver, context);
    resolver.ResolveExpression(Expr, context);
    Contract.Assert(Expr.Type != null); // follows from postcondition of ResolveExpression
    resolver.ConstrainTypeExprBool(Expr, "condition is expected to be of type bool, but is {0}");
    
      // if (stmt is PredicateStmt) {
      //   PredicateStmt s = (PredicateStmt)stmt;
      //   var assertStmt = stmt as AssertStmt;
      //   if (assertStmt != null && assertStmt.Label != null) {
      //     if (DominatingStatementLabels.Find(assertStmt.Label.Name) != null) {
      //       reporter.Error(MessageSource.Resolver, assertStmt.Label.Tok, "assert label shadows a dominating label");
      //     } else {
      //       var rr = DominatingStatementLabels.Push(assertStmt.Label.Name, assertStmt.Label);
      //       Contract.Assert(rr == Scope<Label>.PushResult.Success);  // since we just checked for duplicates, we expect the Push to succeed
      //     }
      //   }
      //
      //   if (assertStmt != null && assertStmt.HasUserAttribute("only", out var attribute)) {
      //     reporter.Warning(MessageSource.Verifier, ResolutionErrors.ErrorId.r_assert_only_assumes_others.ToString(), attribute.RangeToken.ToToken(),
      //       "Assertion with {:only} temporarily transforms other assertions into assumptions");
      //     if (attribute.Args.Count >= 1
      //         && attribute.Args[0] is LiteralExpr { Value: string value }
      //         && value != "before" && value != "after") {
      //       reporter.Warning(MessageSource.Verifier, ResolutionErrors.ErrorId.r_assert_only_before_after.ToString(), attribute.Args[0].RangeToken.ToToken(),
      //         "{:only} only accepts \"before\" or \"after\" as an optional argument");
      //     }
      //   }
      //   ResolveExpression(s.Expr, resolutionContext);
      //   Contract.Assert(s.Expr.Type != null);  // follows from postcondition of ResolveExpression
      //   ConstrainTypeExprBool(s.Expr, "condition is expected to be of type bool, but is {0}");
      //   if (assertStmt != null && assertStmt.Proof != null) {
      //     // clear the labels for the duration of checking the proof body, because break statements are not allowed to leave a the proof body
      //     var prevLblStmts = enclosingStatementLabels;
      //     var prevLoopStack = loopStack;
      //     enclosingStatementLabels = new Scope<Statement>(Options);
      //     loopStack = new List<Statement>();
      //     ResolveStatement(assertStmt.Proof, resolutionContext);
      //     enclosingStatementLabels = prevLblStmts;
      //     loopStack = prevLoopStack;
      //   }
      //   var expectStmt = stmt as ExpectStmt;
      //   if (expectStmt != null) {
      //     if (expectStmt.Message == null) {
      //       expectStmt.Message = new StringLiteralExpr(s.Tok, "expectation violation", false);
      //     }
      //     ResolveExpression(expectStmt.Message, resolutionContext);
      //     Contract.Assert(expectStmt.Message.Type != null);  // follows from postcondition of ResolveExpression
      //   }

  }
}