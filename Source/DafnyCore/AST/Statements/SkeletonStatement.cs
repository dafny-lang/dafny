using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/// <summary>
/// The class represents several possible scenarios:
/// * ...;
///   S == null
/// * assert ...
///   ConditionOmitted == true
/// * assume ...
///   ConditionOmitted == true
/// * if ... { Stmt }
///   if ... { Stmt } else ElseStmt
///   ConditionOmitted == true
/// * while ... invariant J;
///   ConditionOmitted == true && BodyOmitted == true
/// * while ... invariant J; { Stmt }
///   ConditionOmitted == true && BodyOmitted == false
/// * modify ...;
///   ConditionOmitted == true && BodyOmitted == false
/// * modify ... { Stmt }
///   ConditionOmitted == true && BodyOmitted == false
/// </summary>
public class SkeletonStatement : Statement, ICloneable<SkeletonStatement>, ICanFormat {
  public readonly Statement S;
  public bool ConditionOmitted { get { return ConditionEllipsis != null; } }
  public readonly IToken ConditionEllipsis;
  public bool BodyOmitted { get { return BodyEllipsis != null; } }
  public readonly IToken BodyEllipsis;

  public SkeletonStatement Clone(Cloner cloner) {
    return new SkeletonStatement(cloner, this);
  }

  public SkeletonStatement(Cloner cloner, SkeletonStatement original) : base(cloner, original) {
    S = original.S == null ? null : cloner.CloneStmt(original.S);
    ConditionEllipsis = original.ConditionEllipsis;
    BodyEllipsis = original.BodyEllipsis;
  }

  public SkeletonStatement(RangeToken rangeToken)
    : base(rangeToken) {
    Contract.Requires(rangeToken != null);
    S = null;
  }
  public SkeletonStatement(Statement s, IToken conditionEllipsis, IToken bodyEllipsis)
    : base(s.RangeToken) {
    Contract.Requires(s != null);
    S = s;
    ConditionEllipsis = conditionEllipsis;
    BodyEllipsis = bodyEllipsis;
  }
  public override IEnumerable<Statement> SubStatements {
    get {
      // The SkeletonStatement is really a modification of its inner statement S.  Therefore,
      // we don't consider S to be a substatement.  Instead, the substatements of S are the
      // substatements of the SkeletonStatement.  In the case the SkeletonStatement modifies
      // S by omitting its body (which is true only for loops), there are no substatements.
      if (!BodyOmitted && S.SubStatements != null) {
        foreach (var s in S.SubStatements) {
          yield return s;
        }
      }
    }
  }

  public override IEnumerable<Statement> PreResolveSubStatements {
    get {
      yield return S;
    }
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    return true;
  }
}