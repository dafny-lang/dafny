#nullable enable

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
  public Statement? S;
  public bool ConditionOmitted => ConditionEllipsis != null;
  public IOrigin? ConditionEllipsis;
  public bool BodyOmitted => BodyEllipsis != null;
  public IOrigin? BodyEllipsis;

  public SkeletonStatement Clone(Cloner cloner) {
    return new SkeletonStatement(cloner, this);
  }

  public SkeletonStatement(Cloner cloner, SkeletonStatement original) : base(cloner, original) {
    S = original.S == null ? null : cloner.CloneStmt(original.S, false);
    ConditionEllipsis = original.ConditionEllipsis;
    BodyEllipsis = original.BodyEllipsis;
  }

  public SkeletonStatement(IOrigin origin)
    : base(origin) {
    Contract.Requires(origin != null);
    S = null;
  }
  public SkeletonStatement(Statement s, IOrigin conditionEllipsis, IOrigin bodyEllipsis)
    : base(s.Origin) {
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
      if (!BodyOmitted && S?.SubStatements != null) {
        foreach (var s in S.SubStatements) {
          yield return s;
        }
      }
    }
  }

  public override IEnumerable<Statement> PreResolveSubStatements {
    get {
      if (S != null) {
        yield return S;
      }
    }
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    return true;
  }

  public override void ResolveGhostness(ModuleResolver resolver, ErrorReporter reporter, bool mustBeErasable,
    ICodeContext codeContext, string? proofContext,
    bool allowAssumptionVariables, bool inConstructorInitializationPhase) {
    IsGhost = mustBeErasable;
    if (S != null) {
      S.ResolveGhostness(resolver, reporter, mustBeErasable, codeContext, proofContext, allowAssumptionVariables, inConstructorInitializationPhase);
      IsGhost = IsGhost || S.IsGhost;
    }
  }
}