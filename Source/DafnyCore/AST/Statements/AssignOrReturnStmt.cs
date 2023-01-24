using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class AssignOrReturnStmt : ConcreteUpdateStatement, ICloneable<AssignOrReturnStmt> {
  public readonly ExprRhs Rhs; // this is the unresolved RHS, and thus can also be a method call
  public readonly List<AssignmentRhs> Rhss;
  public readonly AttributedToken KeywordToken;
  [FilledInDuringResolution] public readonly List<Statement> ResolvedStatements = new List<Statement>();
  public override IEnumerable<Statement> SubStatements => ResolvedStatements;
  public override IToken Tok {
    get {
      var result = Rhs.StartToken.Prev;
      if (char.IsLetter(result.val[0])) {
        // Jump to operator if we're on an assume/expect/assert keyword.
        result = result.Prev;
      }
      return result;
    }
  }

  public override IEnumerable<Node> Children => ResolvedStatements;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Lhss != null);
    Contract.Invariant(
      Lhss.Count == 0 ||                   // ":- MethodOrExpression;" which returns void success or an error
      (Lhss.Count == 1 && Lhss[0] != null)   // "y :- MethodOrExpression;"
    );
    Contract.Invariant(Rhs != null);
  }

  public AssignOrReturnStmt Clone(Cloner cloner) {
    return new AssignOrReturnStmt(cloner, this);
  }

  public AssignOrReturnStmt(Cloner cloner, AssignOrReturnStmt original) : base(cloner, original) {
    Rhs = (ExprRhs)cloner.CloneRHS(original.Rhs);
    Rhss = original.Rhss.Select(cloner.CloneRHS).ToList();
    KeywordToken = cloner.AttributedTok(original.KeywordToken);

    if (cloner.CloneResolvedFields) {
      ResolvedStatements = original.ResolvedStatements.Select(cloner.CloneStmt).ToList();
    }
  }

  public AssignOrReturnStmt(RangeToken rangeToken, List<Expression> lhss, ExprRhs rhs, AttributedToken keywordToken, List<AssignmentRhs> rhss = null)
    : base(rangeToken, lhss) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(lhss != null);
    Contract.Requires(lhss.Count <= 1);
    Contract.Requires(rhs != null);
    Rhs = rhs;
    Rhss = rhss;
    KeywordToken = keywordToken;
  }
}
