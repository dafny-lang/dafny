#nullable enable

using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class ExpectStmt : PredicateStmt, ICloneable<ExpectStmt>, ICanFormat {
  public Expression? Message;

  public ExpectStmt Clone(Cloner cloner) {
    return new ExpectStmt(cloner, this);
  }

  public ExpectStmt(Cloner cloner, ExpectStmt original) : base(cloner, original) {
    Message = cloner.CloneExpr(original.Message);
  }

  [SyntaxConstructor]
  public ExpectStmt(IOrigin origin, Expression expr, Expression? message, Attributes? attributes = null)
    : base(origin, expr, attributes) {
    Message = message;
  }

  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) { yield return e; }
      yield return Expr;
      if (Message != null) {
        yield return Message;
      }
    }
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    return formatter.SetIndentAssertLikeStatement(this, indentBefore);
  }

  public override void GenResolve(INewOrOldResolver resolver, ResolutionContext context) {
    base.GenResolve(resolver, context);
    if (Message == null) {
      Message = new StringLiteralExpr(Origin, "expectation violation", false);
    }
    resolver.ResolveExpression(Message, context);
  }

  public override void ResolveGhostness(ModuleResolver resolver, ErrorReporter reporter, bool mustBeErasable,
    ICodeContext codeContext,
    string? proofContext, bool allowAssumptionVariables, bool inConstructorInitializationPhase) {
    IsGhost = false;
    if (mustBeErasable) {
      reporter.Error(MessageSource.Resolver, ResolutionErrors.ErrorId.r_expect_statement_is_not_ghost, this,
        "expect statement is not allowed in this context (because this is a ghost method or because the statement is guarded by a specification-only expression)");
    } else {
      ExpressionTester.CheckIsCompilable(resolver, reporter, Expr, codeContext);
      // If not provided, the message is populated with a default value in resolution
      Contract.Assert(Message != null);
      ExpressionTester.CheckIsCompilable(resolver, reporter, Message, codeContext);
    }
  }
}