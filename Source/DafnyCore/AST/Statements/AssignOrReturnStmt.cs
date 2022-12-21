using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class AssignOrReturnStmt : ConcreteUpdateStatement, ICloneable<AssignOrReturnStmt> {
  public readonly ExprRhs Rhs; // this is the unresolved RHS, and thus can also be a method call
  public readonly List<AssignmentRhs> Rhss;
  public readonly AttributedToken KeywordToken;
  [FilledInDuringResolution] public readonly List<Statement> ResolvedStatements = new List<Statement>();
  public override IEnumerable<Statement> SubStatements {
    get { return ResolvedStatements; }
  }

  public override IEnumerable<INode> Children => ResolvedStatements;

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

  public AssignOrReturnStmt(IToken tok, IToken endTok, List<Expression> lhss, ExprRhs rhs, AttributedToken keywordToken, List<AssignmentRhs> rhss = null)
    : base(tok, endTok, lhss) {
    Contract.Requires(tok != null);
    Contract.Requires(endTok != null);
    Contract.Requires(lhss != null);
    Contract.Requires(lhss.Count <= 1);
    Contract.Requires(rhs != null);
    Rhs = rhs;
    Rhss = rhss;
    KeywordToken = keywordToken;
  }
}
