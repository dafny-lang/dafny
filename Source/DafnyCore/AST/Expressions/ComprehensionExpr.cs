using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// A ComprehensionExpr has the form:
///   BINDER { x [: Type] [<- Domain] [Attributes] [| Range] } [:: Term(x)]
/// Where BINDER is currently "forall", "exists", "iset"/"set", or "imap"/"map".
///
/// Quantifications used to only support a single range, but now each
/// quantified variable can have a range attached.
/// The overall Range is now filled in by the parser by extracting any implicit
/// "x in Domain" constraints and per-variable Range constraints into a single conjunct.
///
/// The Term is optional if the expression only has one quantified variable,
/// but required otherwise.
///
/// LambdaExpr also inherits from this base class but isn't really a comprehension,
/// and should be considered implementation inheritance.
/// </summary>
public abstract class ComprehensionExpr : Expression, IAttributeBearingDeclaration, IBoundVarsBearingExpression {
  public virtual string WhatKind => "comprehension";
  public readonly List<BoundVar> BoundVars;
  public readonly Expression Range;
  public Expression Term;

  public IEnumerable<BoundVar> AllBoundVars => BoundVars;

  public IToken BodyStartTok = Token.NoToken;
  public IToken BodyEndTok = Token.NoToken;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(BoundVars != null);
    Contract.Invariant(Term != null);
  }

  public Attributes Attributes;
  Attributes IAttributeBearingDeclaration.Attributes => Attributes;

  public abstract class BoundedPool : ICloneable<BoundedPool> {
    [Flags]
    public enum PoolVirtues { None = 0, Finite = 1, Enumerable = 2, IndependentOfAlloc = 4, IndependentOfAlloc_or_ExplicitAlloc = 8 }
    public abstract PoolVirtues Virtues { get; }
    /// <summary>
    /// A higher preference is better.
    /// A preference below 2 is a last-resort bounded pool. Bounds discovery will not consider
    /// such a pool to be final until there are no other choices.
    ///
    /// For easy reference, here is the BoundedPool hierarchy and their preference levels:
    ///
    /// 0: AllocFreeBoundedPool
    /// 0: ExplicitAllocatedBoundedPool
    /// 0: SpecialAllocIndependenceAllocatedBoundedPool
    /// 0: OlderBoundedPool
    ///
    /// 1: WiggleWaggleBound
    ///
    /// 2: SuperSetBoundedPool
    /// 2: DatatypeInclusionBoundedPool
    ///
    /// 3: SubSetBoundedPool
    ///
    /// 4: IntBoundedPool with one bound
    /// 5: IntBoundedPool with both bounds
    /// 5: CharBoundedPool
    ///
    /// 8: DatatypeBoundedPool
    ///
    /// 10: CollectionBoundedPool
    ///     - SetBoundedPool
    ///     - MapBoundedPool
    ///     - SeqBoundedPool
    ///
    /// 14: BoolBoundedPool
    ///
    /// 15: ExactBoundedPool
    /// </summary>
    public abstract int Preference(); // higher is better

    public static BoundedPool GetBest(List<BoundedPool> bounds, PoolVirtues requiredVirtues) {
      Contract.Requires(bounds != null);
      bounds = CombineIntegerBounds(bounds);
      BoundedPool best = null;
      foreach (var bound in bounds) {
        if ((bound.Virtues & requiredVirtues) == requiredVirtues) {
          if (best == null || bound.Preference() > best.Preference()) {
            best = bound;
          }
        }
      }
      return best;
    }
    public static List<VT> MissingBounds<VT>(List<VT> vars, List<BoundedPool> bounds, PoolVirtues requiredVirtues = PoolVirtues.None) where VT : IVariable {
      Contract.Requires(vars != null);
      Contract.Requires(bounds == null || vars.Count == bounds.Count);
      Contract.Ensures(Contract.Result<List<VT>>() != null);
      var missing = new List<VT>();
      for (var i = 0; i < vars.Count; i++) {
        if (bounds == null || bounds[i] == null || (bounds[i].Virtues & requiredVirtues) != requiredVirtues) {
          missing.Add(vars[i]);
        }
      }
      return missing;
    }
    public static List<bool> HasBounds(List<BoundedPool> bounds, PoolVirtues requiredVirtues = PoolVirtues.None) {
      Contract.Requires(bounds != null);
      Contract.Ensures(Contract.Result<List<bool>>() != null);
      Contract.Ensures(Contract.Result<List<bool>>().Count == bounds.Count);
      return bounds.ConvertAll(bound => bound != null && (bound.Virtues & requiredVirtues) == requiredVirtues);
    }
    static List<BoundedPool> CombineIntegerBounds(List<BoundedPool> bounds) {
      var lowerBounds = new List<IntBoundedPool>();
      var upperBounds = new List<IntBoundedPool>();
      var others = new List<BoundedPool>();
      foreach (var b in bounds) {
        var ib = b as IntBoundedPool;
        if (ib != null && ib.UpperBound == null) {
          lowerBounds.Add(ib);
        } else if (ib != null && ib.LowerBound == null) {
          upperBounds.Add(ib);
        } else {
          others.Add(b);
        }
      }
      // pair up the bounds
      var n = Math.Min(lowerBounds.Count, upperBounds.Count);
      for (var i = 0; i < n; i++) {
        others.Add(new IntBoundedPool(lowerBounds[i].LowerBound, upperBounds[i].UpperBound));
      }
      for (var i = n; i < lowerBounds.Count; i++) {
        others.Add(lowerBounds[i]);
      }
      for (var i = n; i < upperBounds.Count; i++) {
        others.Add(upperBounds[i]);
      }
      return others;
    }

    public abstract BoundedPool Clone(Cloner cloner);
  }
  public class ExactBoundedPool : BoundedPool {
    public readonly Expression E;
    public ExactBoundedPool(Expression e) {
      Contract.Requires(e != null);
      E = e;
    }
    public override PoolVirtues Virtues => PoolVirtues.Finite | PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
    public override int Preference() => 15;  // the best of all bounds
    public override BoundedPool Clone(Cloner cloner) {
      return new ExactBoundedPool(cloner.CloneExpr(E));
    }
  }
  public class BoolBoundedPool : BoundedPool {
    public override PoolVirtues Virtues => PoolVirtues.Finite | PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
    public override int Preference() => 14;
    public override BoundedPool Clone(Cloner cloner) {
      return this;
    }
  }
  public class CharBoundedPool : BoundedPool {
    public override PoolVirtues Virtues => PoolVirtues.Finite | PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
    public override int Preference() => 5;
    public override BoundedPool Clone(Cloner cloner) {
      return this;
    }
  }
  public class AllocFreeBoundedPool : BoundedPool {
    public Type Type;
    public AllocFreeBoundedPool(Type t) {
      Type = t;
    }
    public override PoolVirtues Virtues {
      get {
        if (Type.IsRefType) {
          return PoolVirtues.Finite | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
        } else {
          return PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
        }
      }
    }
    public override int Preference() => 0;
    public override BoundedPool Clone(Cloner cloner) {
      return this;
    }
  }
  public class ExplicitAllocatedBoundedPool : BoundedPool {
    public ExplicitAllocatedBoundedPool() {
    }
    public override PoolVirtues Virtues => PoolVirtues.Finite | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
    public override int Preference() => 0;
    public override BoundedPool Clone(Cloner cloner) {
      return this;
    }
  }
  public class SpecialAllocIndependenceAllocatedBoundedPool : BoundedPool {
    public SpecialAllocIndependenceAllocatedBoundedPool() {
    }
    public override PoolVirtues Virtues => PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
    public override int Preference() => 0;
    public override BoundedPool Clone(Cloner cloner) {
      return this;
    }
  }
  public class IntBoundedPool : BoundedPool {
    public readonly Expression LowerBound;
    public readonly Expression UpperBound;
    public IntBoundedPool(Expression lowerBound, Expression upperBound) {
      Contract.Requires(lowerBound != null || upperBound != null);
      LowerBound = lowerBound;
      UpperBound = upperBound;
    }
    public override PoolVirtues Virtues {
      get {
        if (LowerBound != null && UpperBound != null) {
          return PoolVirtues.Finite | PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
        } else {
          return PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
        }
      }
    }
    public override int Preference() => LowerBound != null && UpperBound != null ? 5 : 4;
    public override BoundedPool Clone(Cloner cloner) {
      return new IntBoundedPool(cloner.CloneExpr(LowerBound), cloner.CloneExpr(UpperBound));
    }
  }
  public abstract class CollectionBoundedPool : BoundedPool {
    public readonly Type BoundVariableType;
    public readonly Type CollectionElementType;
    public readonly bool IsFiniteCollection;

    public CollectionBoundedPool(Type bvType, Type collectionElementType, bool isFiniteCollection) {
      Contract.Requires(bvType != null);
      Contract.Requires(collectionElementType != null);

      BoundVariableType = bvType;
      CollectionElementType = collectionElementType;
      IsFiniteCollection = isFiniteCollection;
    }

    public override PoolVirtues Virtues {
      get {
        var v = PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
        if (IsFiniteCollection) {
          v |= PoolVirtues.Finite;
          if (CollectionElementType.IsTestableToBe(BoundVariableType)) {
            v |= PoolVirtues.Enumerable;
          }
        }
        return v;
      }
    }
    public override int Preference() => 10;
  }
  public class SetBoundedPool : CollectionBoundedPool {
    public readonly Expression Set;

    public SetBoundedPool(Expression set, Type bvType, Type collectionElementType, bool isFiniteCollection)
      : base(bvType, collectionElementType, isFiniteCollection) {
      Contract.Requires(set != null);
      Contract.Requires(bvType != null);
      Contract.Requires(collectionElementType != null);
      Set = set;
    }

    public override BoundedPool Clone(Cloner cloner) {
      return new SetBoundedPool(cloner.CloneExpr(Set), BoundVariableType, CollectionElementType, IsFiniteCollection);
    }
  }
  public class SubSetBoundedPool : BoundedPool {
    public readonly Expression UpperBound;
    public readonly bool IsFiniteCollection;
    public SubSetBoundedPool(Expression set, bool isFiniteCollection) {
      UpperBound = set;
      IsFiniteCollection = isFiniteCollection;
    }
    public override PoolVirtues Virtues {
      get {
        if (IsFiniteCollection) {
          return PoolVirtues.Finite | PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
        } else {
          // it's still enumerable, because at run time, all sets are finite after all
          return PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
        }
      }
    }
    public override int Preference() => 3;
    public override BoundedPool Clone(Cloner cloner) {
      return new SubSetBoundedPool(cloner.CloneExpr(UpperBound), IsFiniteCollection);
    }
  }
  public class SuperSetBoundedPool : BoundedPool {
    public readonly Expression LowerBound;
    public SuperSetBoundedPool(Expression set) { LowerBound = set; }
    public override int Preference() => 2;
    public override BoundedPool Clone(Cloner cloner) {
      return new SuperSetBoundedPool(cloner.CloneExpr(LowerBound));
    }

    public override PoolVirtues Virtues {
      get {
        if (LowerBound.Type.MayInvolveReferences) {
          return PoolVirtues.None;
        } else {
          return PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
        }
      }
    }
  }
  public class MultiSetBoundedPool : CollectionBoundedPool {
    public readonly Expression MultiSet;

    public MultiSetBoundedPool(Expression multiset, Type bvType, Type collectionElementType)
      : base(bvType, collectionElementType, true) {
      Contract.Requires(multiset != null);
      Contract.Requires(bvType != null);
      Contract.Requires(collectionElementType != null);
      MultiSet = multiset;
    }

    public override BoundedPool Clone(Cloner cloner) {
      return new MultiSetBoundedPool(cloner.CloneExpr(MultiSet), BoundVariableType, CollectionElementType);
    }
  }
  public class MapBoundedPool : CollectionBoundedPool {
    public readonly Expression Map;

    public MapBoundedPool(Expression map, Type bvType, Type collectionElementType, bool isFiniteCollection)
      : base(bvType, collectionElementType, isFiniteCollection) {
      Contract.Requires(map != null);
      Contract.Requires(bvType != null);
      Contract.Requires(collectionElementType != null);
      Map = map;
    }
    public override BoundedPool Clone(Cloner cloner) {
      return new MapBoundedPool(cloner.CloneExpr(Map), BoundVariableType, CollectionElementType, IsFiniteCollection);
    }
  }
  public class SeqBoundedPool : CollectionBoundedPool {
    public readonly Expression Seq;

    public SeqBoundedPool(Expression seq, Type bvType, Type collectionElementType)
      : base(bvType, collectionElementType, true) {
      Contract.Requires(seq != null);
      Contract.Requires(bvType != null);
      Contract.Requires(collectionElementType != null);
      Seq = seq;
    }

    public override BoundedPool Clone(Cloner cloner) {
      return new SeqBoundedPool(cloner.CloneExpr(Seq), BoundVariableType, CollectionElementType);
    }
  }
  public class DatatypeBoundedPool : BoundedPool {
    public readonly DatatypeDecl Decl;

    public DatatypeBoundedPool(DatatypeDecl d) {
      Contract.Requires(d != null);
      Decl = d;
    }
    public override PoolVirtues Virtues => PoolVirtues.Finite | PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
    public override int Preference() => 8;
    public override BoundedPool Clone(Cloner cloner) {
      return this;
    }
  }
  public class DatatypeInclusionBoundedPool : BoundedPool {
    public readonly bool IsIndDatatype;
    public DatatypeInclusionBoundedPool(bool isIndDatatype) : base() { IsIndDatatype = isIndDatatype; }
    public override PoolVirtues Virtues => (IsIndDatatype ? PoolVirtues.Finite : PoolVirtues.None) | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
    public override int Preference() => 2;
    public override BoundedPool Clone(Cloner cloner) {
      return this;
    }
  }

  public class OlderBoundedPool : BoundedPool {
    public OlderBoundedPool() {
    }
    public override PoolVirtues Virtues => PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
    public override int Preference() => 0;
    public override BoundedPool Clone(Cloner cloner) {
      return this;
    }
  }

  [FilledInDuringResolution] public List<BoundedPool> Bounds;
  // invariant Bounds == null || Bounds.Count == BoundVars.Count;

  public List<BoundVar> UncompilableBoundVars() {
    Contract.Ensures(Contract.Result<List<BoundVar>>() != null);
    var v = BoundedPool.PoolVirtues.Finite | BoundedPool.PoolVirtues.Enumerable;
    return ComprehensionExpr.BoundedPool.MissingBounds(BoundVars, Bounds, v);
  }

  protected ComprehensionExpr(RangeToken rangeToken, List<BoundVar> bvars, Expression range, Expression term, Attributes attrs)
    : base(rangeToken) {
    Contract.Requires(tok != null);
    Contract.Requires(cce.NonNullElements(bvars));
    Contract.Requires(term != null);

    this.BoundVars = bvars;
    this.Range = range;
    this.Term = term;
    this.Attributes = attrs;
    this.BodyStartTok = tok;
  }

  protected ComprehensionExpr(Cloner cloner, ComprehensionExpr original) : base(cloner, original) {
    BoundVars = original.BoundVars.Select(bv => cloner.CloneBoundVar(bv, false)).ToList();
    Range = cloner.CloneExpr(original.Range);
    Attributes = cloner.CloneAttributes(original.Attributes);
    BodyStartTok = cloner.Tok(original.BodyStartTok);
    RangeToken = cloner.Tok(original.RangeToken);
    Term = cloner.CloneExpr(original.Term);

    if (cloner.CloneResolvedFields) {
      Bounds = original.Bounds?.Select(b => b?.Clone(cloner)).ToList();
    }
  }
  public override IEnumerable<Node> Children => (Attributes != null ? new List<Node> { Attributes } : Enumerable.Empty<Node>()).Concat(SubExpressions);

  public override IEnumerable<Expression> SubExpressions {
    get {
      foreach (var e in Attributes.SubExpressions(Attributes)) {
        yield return e;
      }
      if (Range != null) { yield return Range; }
      yield return Term;
    }
  }

  public override IEnumerable<Type> ComponentTypes => BoundVars.Select(bv => bv.Type);
}
