using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class AlternativeStmt : Statement, ICloneable<AlternativeStmt> {
  public readonly bool UsesOptionalBraces;
  public readonly List<GuardedAlternative> Alternatives;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Alternatives != null);
  }

  public AlternativeStmt Clone(Cloner cloner) {
    return new AlternativeStmt(cloner, this);
  }

  public AlternativeStmt(Cloner cloner, AlternativeStmt original) : base(cloner, original) {
    Alternatives = original.Alternatives.ConvertAll(cloner.CloneGuardedAlternative);
    UsesOptionalBraces = original.UsesOptionalBraces;
  }

  public AlternativeStmt(IToken tok, RangeToken rangeToken, List<GuardedAlternative> alternatives, bool usesOptionalBraces)
    : base(tok, rangeToken) {
    Contract.Requires(tok != null);
    Contract.Requires(alternatives != null);
    this.Alternatives = alternatives;
    this.UsesOptionalBraces = usesOptionalBraces;
  }
  public AlternativeStmt(IToken tok, RangeToken rangeToken, List<GuardedAlternative> alternatives, bool usesOptionalBraces, Attributes attrs)
    : base(tok, rangeToken, attrs) {
    Contract.Requires(tok != null);
    Contract.Requires(alternatives != null);
    this.Alternatives = alternatives;
    this.UsesOptionalBraces = usesOptionalBraces;
  }
  public override IEnumerable<Statement> SubStatements {
    get {
      foreach (var alt in Alternatives) {
        foreach (var s in alt.Body) {
          yield return s;
        }
      }
    }
  }
  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) { yield return e; }
      foreach (var alt in Alternatives) {
        yield return alt.Guard;
      }
    }
  }

  public override IEnumerable<Node> Children => Alternatives;
}