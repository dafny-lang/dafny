#nullable enable

using System;
using System.Collections.Generic;
using System.Diagnostics;

namespace Microsoft.Dafny;

public abstract class QuantifierExpr : ComprehensionExpr, TypeParameter.ParentType {
  public override string WhatKind => "quantifier";

  private int UniqueId;
  private static int currentQuantId = -1;

  protected virtual BinaryExpr.ResolvedOpcode SplitResolvedOp => BinaryExpr.ResolvedOpcode.Or;

  /// <summary>
  /// The parts that the trigger generator split the quantifier into and selected triggers for, which the verifier
  /// translates instead of it, or null if it did not split the quantifier
  /// </summary>
  internal List<QuantifierExpr>? Parts() {
    return Triggers.QuantifierSplitter.Parts(this);
  }

  /// <summary>
  /// The conjunction of the parts, for a forall, or their disjunction
  /// </summary>
  internal Expression? PartsExpression() {
    var parts = Parts();
    if (parts == null) {
      return null;
    }
    Expression accumulator = parts[0];
    for (int tid = 1; tid < parts.Count; tid++) {
      accumulator = new BinaryExpr(Term.Origin, SplitResolvedOp, accumulator, parts[tid]);
    }
    return accumulator;
  }

  static int FreshQuantId() {
    return System.Threading.Interlocked.Increment(ref currentQuantId);
  }

  public string FullName {
    get {
      return "q$" + UniqueId;
    }
  }

  public String Refresh(string prefix, FreshIdGenerator idGen) {
    return idGen.FreshId(prefix);
  }

  [SyntaxConstructor]
  protected QuantifierExpr(
    IOrigin origin, List<BoundVar> boundVars, Expression? range, Expression term, Attributes? attributes = null)
    : base(origin, boundVars, range, term, attributes) {
    this.UniqueId = FreshQuantId();
  }

  protected QuantifierExpr(Cloner cloner, QuantifierExpr original) : base(cloner, original) {
    this.UniqueId = FreshQuantId();
  }

  public abstract Expression LogicalBody();

  public override IEnumerable<INode> PreResolveChildren => base.SubExpressions;
  public IEnumerable<Expression> PreResolveSubExpressions => base.SubExpressions;

  public override IEnumerable<Expression> SubExpressions {
    get {
      foreach (var e in base.SubExpressions) {
        yield return e;
      }
      foreach (var e in Attributes.SubExpressions(Attributes)) {
        yield return e;
      }
    }
  }
}
