using JetBrains.Annotations;

namespace Microsoft.Dafny;

/// <summary>
/// Looks for every non-ghost comprehensions, and if they are using a subset type,
/// check that the subset constraint is compilable. If it is not compilable, raises an error.
/// </summary>
public class SubsetConstraintGhostChecker : ProgramTraverser {
  private class FirstErrorCollector : ErrorReporter {
    public string FirstCollectedMessage = "";
    public IOrigin FirstCollectedToken = Token.NoToken;
    public bool Collected = false;

    public bool Message(MessageSource source, ErrorLevel level, IOrigin tok, string msg) {
      return Message(source, level, ErrorRegistry.NoneId, tok, msg);
    }

    protected override bool MessageCore(MessageSource source, ErrorLevel level, string errorId, IOrigin tok, string msg) {
      if (!Collected && level == ErrorLevel.Error) {
        FirstCollectedMessage = msg;
        FirstCollectedToken = tok;
        Collected = true;
      }
      return true;
    }

    public override int Count(ErrorLevel level) {
      return level == ErrorLevel.Error && Collected ? 1 : 0;
    }

    public override int CountExceptVerifierAndCompiler(ErrorLevel level) {
      return Count(level);
    }

    public FirstErrorCollector(DafnyOptions options) : base(options) {
    }
  }

  public ErrorReporter reporter;

  public SubsetConstraintGhostChecker(ErrorReporter reporter) {
    this.reporter = reporter;
  }

  protected override ContinuationStatus OnEnter(Statement stmt, string field, object parent) {
    return stmt != null && stmt.IsGhost ? skip : ok;
  }

  protected override ContinuationStatus OnEnter(MemberDecl memberDecl, string field, object parent) {
    // Includes functions and methods as well.
    // Ghost functions can have a compiled implementation.
    // We want to recurse only on the by method, not on the sub expressions of the function
    if (memberDecl == null || !memberDecl.IsGhost) { return ok; }
    if (memberDecl is Function f) {
      if (f.ByMethodDecl != null && Traverse(f.ByMethodDecl, "ByMethodDecl", f)) { return stop; }
      if (f.ByMethodDecl == null || f.ByMethodDecl.Body != f.ByMethodBody) {
        if (f.ByMethodBody != null && Traverse(f.ByMethodBody, "ByMethodBody", f)) { return stop; }
      }
    }
    return skip;
  }

  private bool IsFieldSpecification(string field, object parent) {
    return field != null && parent != null && (
      (parent is Statement && field == "SpecificationSubExpressions") ||
      (parent is Function && (field is "Req.E" or "Reads.E" or "Ens.E" or "Decreases.Expressions")) ||
      (parent is Method && (field is "Req.E" or "Reads.E" or "Mod.E" or "Ens.E" or "Decreases.Expressions"))
    );
  }

  public override bool Traverse(Expression expr, [CanBeNull] string field, [CanBeNull] object parent) {
    if (expr == null) {
      return false;
    }
    if (IsFieldSpecification(field, parent)) {
      return false;
    }
    // Since we skipped ghost code, the code has to be compiled here. 
    if (expr is not ComprehensionExpr e) {
      return base.Traverse(expr, field, parent);
    }

    if (e is QuantifierExpr or SetComprehension or MapComprehension) {
      foreach (var boundVar in e.BoundVars) {
        if (boundVar.Type.NormalizeExpandKeepConstraints().AsRedirectingType is (SubsetTypeDecl or NewtypeDecl) and var declWithConstraints) {
          if (!declWithConstraints.ConstraintIsCompilable) {

            IOrigin finalToken = boundVar.Tok;
            if (declWithConstraints.Constraint != null && declWithConstraints.Constraint.Tok.line != 0) {
              var errorCollector = new FirstErrorCollector(reporter.Options);
              ExpressionTester.CheckIsCompilable(null, errorCollector, declWithConstraints.Constraint,
                new CodeContextWrapper(declWithConstraints, true));
              if (errorCollector.Collected) {
                finalToken = new NestedOrigin(finalToken, errorCollector.FirstCollectedToken,
                  "The constraint is not compilable because " + errorCollector.FirstCollectedMessage
                );
              }
            }
            this.reporter.Error(MessageSource.Resolver, finalToken,
              $"{boundVar.Type} is a {declWithConstraints.WhatKind} and its constraint is not compilable, " +
              $"hence it cannot yet be used as the type of a bound variable in {e.WhatKind}.");
          }
        }
      }
    }
    return base.Traverse(e, field, parent);
  }
}
