using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public abstract class ProduceStmt : Statement {
  public List<AssignmentRhs> Rhss;
  [FilledInDuringResolution]
  public UpdateStmt HiddenUpdate;

  protected ProduceStmt(Cloner cloner, ProduceStmt original) : base(cloner, original) {
    if (original.Rhss != null) {
      Rhss = original.Rhss.Select(cloner.CloneRHS).ToList();
    }
    if (cloner.CloneResolvedFields) {
      if (original.HiddenUpdate != null) {
        HiddenUpdate = new UpdateStmt(cloner, original.HiddenUpdate);
      }
    }
  }

  public ProduceStmt(RangeToken rangeToken, List<AssignmentRhs> rhss)
    : base(rangeToken) {
    this.Rhss = rhss;
    HiddenUpdate = null;
  }

  public override IEnumerable<Node> Children =>
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
}