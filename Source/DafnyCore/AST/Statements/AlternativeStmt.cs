using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class AlternativeStmt : Statement, ICloneable<AlternativeStmt>, ICanFormat {
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

  public AlternativeStmt(RangeToken rangeToken, List<GuardedAlternative> alternatives, bool usesOptionalBraces)
    : base(rangeToken) {
    Contract.Requires(alternatives != null);
    this.Alternatives = alternatives;
    this.UsesOptionalBraces = usesOptionalBraces;
  }
  public AlternativeStmt(RangeToken rangeToken, List<GuardedAlternative> alternatives, bool usesOptionalBraces, Attributes attrs)
    : base(rangeToken, attrs) {
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
  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    return formatter.SetIndentCases(indentBefore, OwnedTokens.Concat(Alternatives.SelectMany(alternative => alternative.OwnedTokens)).OrderBy(token => token.pos), () => {
      formatter.VisitAlternatives(Alternatives, indentBefore);
    });
  }
}