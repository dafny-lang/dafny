#nullable enable
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public abstract class ProduceStmt : Statement {
  public List<AssignmentRhs>? Rhss;
  [FilledInDuringResolution]
  public AssignStatement? HiddenUpdate;

  protected ProduceStmt(Cloner cloner, ProduceStmt original) : base(cloner, original) {
    if (original.Rhss != null) {
      Rhss = original.Rhss.Select(cloner.CloneRHS).ToList();
    }
    if (cloner.CloneResolvedFields) {
      if (original.HiddenUpdate != null) {
        HiddenUpdate = new AssignStatement(cloner, original.HiddenUpdate);
      }
    }
  }

  [SyntaxConstructor]
  protected ProduceStmt(IOrigin origin, List<AssignmentRhs>? rhss, Attributes? attributes)
    : base(origin, attributes) {
    this.Rhss = rhss;
    HiddenUpdate = null;
  }

  public override IEnumerable<INode> Children =>
    HiddenUpdate == null ? base.Children : new Node[] { HiddenUpdate }.Concat(base.Children);

  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) { yield return e; }
      foreach (var rhs in Rhss ?? Enumerable.Empty<AssignmentRhs>()) {
        foreach (var e in rhs.NonSpecificationSubExpressions) {
          yield return e;
        }
      }
    }
  }
  public override IEnumerable<Expression> SpecificationSubExpressions {
    get {
      foreach (var e in base.SpecificationSubExpressions) { yield return e; }
      foreach (var rhs in Rhss ?? Enumerable.Empty<AssignmentRhs>()) {
        foreach (var e in rhs.SpecificationSubExpressions) {
          yield return e;
        }
      }
    }
  }
  public override IEnumerable<Statement> SubStatements {
    get {
      foreach (var rhs in Rhss ?? Enumerable.Empty<AssignmentRhs>()) {
        foreach (var s in rhs.SubStatements) {
          yield return s;
        }
      }
    }
  }

  public override IEnumerable<Statement> PreResolveSubStatements {
    get {
      if (Rhss != null) {
        foreach (var rhs in Rhss) {
          foreach (var s in rhs.PreResolveSubStatements) {
            yield return s;
          }
        }
      }
    }
  }

  public override void ResolveGhostness(ModuleResolver resolver, ErrorReporter reporter, bool mustBeErasable,
    ICodeContext codeContext,
    string? proofContext, bool allowAssumptionVariables, bool inConstructorInitializationPhase) {
    var kind = this is YieldStmt ? "yield" : "return";
    if (mustBeErasable && !codeContext.IsGhost) {
      reporter.Error(MessageSource.Resolver, ResolutionErrors.ErrorId.r_produce_statement_not_allowed_in_ghost, this,
        "{0} statement is not allowed in this context (because it is guarded by a specification-only expression)", kind);
    }

    this.HiddenUpdate?.ResolveGhostness(resolver, reporter, mustBeErasable, codeContext, proofContext,
      allowAssumptionVariables, inConstructorInitializationPhase);
  }
}