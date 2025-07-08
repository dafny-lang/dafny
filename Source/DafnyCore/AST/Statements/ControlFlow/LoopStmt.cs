using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public abstract class LoopStmt : LabeledStatement, IHasNavigationToken {
  public List<AttributedExpression> Invariants;
  public Specification<Expression> Decreases;

  [FilledInDuringResolution] public bool InferredDecreases;  // says that no explicit "decreases" clause was given and an attempt was made to find one automatically (which may or may not have produced anything)
  public Specification<FrameExpression> Mod;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(cce.NonNullElements(Invariants));
    Contract.Invariant(Decreases != null);
    Contract.Invariant(Mod != null);
  }

  protected LoopStmt(Cloner cloner, LoopStmt original) : base(cloner, original) {
    Invariants = original.Invariants.ConvertAll(cloner.CloneAttributedExpr);
    Decreases = cloner.CloneSpecExpr(original.Decreases);
    Mod = cloner.CloneSpecFrameExpr(original.Mod);

    if (cloner.CloneResolvedFields) {
      InferredDecreases = original.InferredDecreases;
    }
  }

  protected LoopStmt(IOrigin origin, List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod)
    : base(origin, [], null) {
    Contract.Requires(origin != null);
    Contract.Requires(cce.NonNullElements(invariants));
    Contract.Requires(decreases != null);
    Contract.Requires(mod != null);

    this.Invariants = invariants;
    this.Decreases = decreases;
    this.Mod = mod;
  }

  [SyntaxConstructor]
  protected LoopStmt(IOrigin origin, List<AttributedExpression> invariants, Specification<Expression> decreases,
    Specification<FrameExpression> mod, List<Label> labels, Attributes attributes)
    : base(origin, labels, attributes) {
    Contract.Requires(origin != null);
    Contract.Requires(cce.NonNullElements(invariants));
    Contract.Requires(decreases != null);
    Contract.Requires(mod != null);

    this.Invariants = invariants;
    this.Decreases = decreases;
    this.Mod = mod;
  }
  public IEnumerable<Expression> LoopSpecificationExpressions {
    get {
      foreach (var mfe in Invariants) {
        foreach (var e in Attributes.SubExpressions(mfe.Attributes)) { yield return e; }
        yield return mfe.E;
      }
      foreach (var e in Attributes.SubExpressions(Decreases.Attributes)) { yield return e; }
      if (Decreases.Expressions != null) {
        foreach (var e in Decreases.Expressions) {
          yield return e;
        }
      }
      foreach (var e in Attributes.SubExpressions(Mod.Attributes)) { yield return e; }
      if (Mod.Expressions != null) {
        foreach (var fe in Mod.Expressions) {
          yield return fe.E;
        }
      }
    }
  }

  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) {
        yield return e;
      }
    }
  }

  public override IEnumerable<Expression> SpecificationSubExpressions {
    get {
      foreach (var e in LoopSpecificationExpressions) {
        yield return e;
      }
    }
  }

  public TokenRange NavigationRange => ReportingRange;
}