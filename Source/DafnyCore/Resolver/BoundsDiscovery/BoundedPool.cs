//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Numerics;

namespace Microsoft.Dafny;

public abstract class BoundedPool : ICloneable<BoundedPool> {
  [Flags]
  public enum PoolVirtues {
    None = 0,
    Finite = 1,
    Enumerable = 2,
    IndependentOfAlloc = 4,
    IndependentOfAlloc_or_ExplicitAlloc = 8
  }

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
  ///     - MultiSetBoundedPool
  ///     - MapBoundedPool
  ///     - SeqBoundedPool
  ///
  /// 14: BoolBoundedPool
  ///
  /// 15: ExactBoundedPool
  /// </summary>
  public abstract int Preference(); // higher is better

  public static BoundedPool GetBest(List<BoundedPool> bounds) {
    Contract.Requires(bounds != null);
    bounds = CombineIntegerBounds(bounds);
    BoundedPool best = null;
    foreach (var bound in bounds) {
      if (best is IntBoundedPool ibp0 && bound is IntBoundedPool ibp1) {
        best = new IntBoundedPool(
          ChooseIntegerBounds(ibp0.LowerBounds.Concat(ibp1.LowerBounds), true),
          ChooseIntegerBounds(ibp0.UpperBounds.Concat(ibp1.UpperBounds), false));
      } else if (best == null || bound.Preference() > best.Preference()) {
        best = bound;
      }
    }
    return best;
  }

  /// <summary>
  /// Returns the bounds, all on one side of a variable, that its enumeration has to take the largest ("pickMax") or the
  /// smallest of at run time, in the order given. Of the constant bounds, only the tightest is kept, in the place of the
  /// first, and only if no other bound kept implies it (see "Implies"). The other bounds cannot be compared statically,
  /// so they are kept, except that one whose evaluation can fail is kept only if it comes first. A range is computed
  /// before the compiled code checks the conjuncts that such a bound may rely on, like the "0 < k" of "i < 100 / k", so
  /// a further one could fail where no element is in the range anyway, while a range with no further bound computes the
  /// first one too.
  /// </summary>
  static List<Expression> ChooseIntegerBounds(IEnumerable<Expression> bounds, bool pickMax) {
    Expression constantBound = null;
    BigInteger constant = default;
    var constantIndex = 0;
    var others = new List<Expression>();
    var first = true;
    foreach (var bound in bounds) {
      if (ConstantFolder.TryFoldInteger(bound) is { } value) {
        if (constantBound == null) {
          constantIndex = others.Count;
        }
        if (constantBound == null || (pickMax ? constant < value : value < constant)) {
          constantBound = bound;
          constant = value;
        }
      } else if (first || CannotFail(bound)) {
        others.Add(bound);
      }
      first = false;
    }
    if (constantBound != null && !others.Exists(other => Implies(other, constant, pickMax))) {
      others.Insert(constantIndex, constantBound);
    }
    return others;
  }

  /// <summary>
  /// Returns whether "bound" is at least "constant" ("pickMax"), or as an exclusive upper bound at most it, wherever it
  /// is evaluated. A variable, a field, a function result, an element, or a length lies in the range of its type, and so
  /// does such a value plus a constant offset, shifted by the offset. Any other bound can lie outside the range of its
  /// type: one that bounds discovery computed, like the "i - 49" that "i < j + 50" gives "j", or one that the compiled
  /// code evaluates where a conjunct it relies on does not hold, like the "n - 1" next to "n > 0".
  /// </summary>
  static bool Implies(Expression bound, BigInteger constant, bool pickMax) {
    var offset = BigInteger.Zero;
    var e = bound.Resolved;
    while (e is BinaryExpr { ResolvedOp: BinaryExpr.ResolvedOpcode.Add or BinaryExpr.ResolvedOpcode.Sub } binary &&
           ConstantFolder.TryFoldInteger(binary.E1) is { } k) {
      offset += binary.ResolvedOp == BinaryExpr.ResolvedOpcode.Add ? k : -k;
      e = binary.E0.Resolved;
    }
    if (e is not (IdentifierExpr or MemberSelectExpr or FunctionCallExpr or SeqSelectExpr or UnaryOpExpr {
      ResolvedOp: UnaryOpExpr.ResolvedOpcode.SeqLength or UnaryOpExpr.ResolvedOpcode.SetCard
      or UnaryOpExpr.ResolvedOpcode.MultiSetCard or UnaryOpExpr.ResolvedOpcode.MapCard
    })) {
      return false;
    }
    var (lower, upper) = ModuleResolver.TypeImpliedIntegerBounds(e.Type);
    return pickMax ? constant <= lower + offset : upper - 1 + offset <= constant;
  }

  /// <summary>
  /// Returns whether evaluating "expr" cannot fail, as a division by a variable, a call, or an index can. A call can
  /// fail without a "requires" too, since the type of a parameter can be constrained.
  /// </summary>
  static bool CannotFail(Expression expr) {
    expr = expr.Resolved;
    bool NonNull(Expression receiver) =>
      receiver == null || (CannotFail(receiver) && (!receiver.Type.IsRefType || receiver.Type.IsNonNullRefType));
    return expr switch {
      LiteralExpr or IdentifierExpr or ThisExpr => true,
      MemberSelectExpr { Member: Field and not DatatypeDestructor } select => NonNull(select.Obj),
      UnaryOpExpr {
        ResolvedOp: UnaryOpExpr.ResolvedOpcode.SeqLength or UnaryOpExpr.ResolvedOpcode.SetCard
        or UnaryOpExpr.ResolvedOpcode.MultiSetCard or UnaryOpExpr.ResolvedOpcode.MapCard
      } cardinality => CannotFail(cardinality.E),
      ConversionExpr conversion => conversion.Type.IsIntegerType && CannotFail(conversion.E),
      BinaryExpr { ResolvedOp: BinaryExpr.ResolvedOpcode.Add or BinaryExpr.ResolvedOpcode.Sub or BinaryExpr.ResolvedOpcode.Mul } binary =>
        CannotFail(binary.E0) && CannotFail(binary.E1),
      BinaryExpr { ResolvedOp: BinaryExpr.ResolvedOpcode.Div or BinaryExpr.ResolvedOpcode.Mod } binary =>
        ConstantFolder.TryFoldInteger(binary.E1) is { IsZero: false } && CannotFail(binary.E0),
      _ => false
    };
  }

  public static List<VT> MissingBounds<VT>(List<VT> vars, List<BoundedPool> bounds, PoolVirtues requiredVirtues) where VT : IVariable {
    Contract.Requires(vars != null);
    Contract.Requires(bounds == null || vars.Count == bounds.Count);
    Contract.Ensures(Contract.Result<List<VT>>() != null);
    var missing = new List<VT>();
    for (var i = 0; i < vars.Count; i++) {
      if (bounds == null || bounds[i] == null ||
          (bounds[i].Virtues & requiredVirtues) != requiredVirtues ||
          ((requiredVirtues & PoolVirtues.Enumerable) != 0 && !bounds[i].IsCompilable(vars[i].Type))) {
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
      others.Add(new IntBoundedPool(lowerBounds[i].LowerBounds, upperBounds[i].UpperBounds));
    }
    for (var i = n; i < lowerBounds.Count; i++) {
      others.Add(lowerBounds[i]);
    }
    for (var i = n; i < upperBounds.Count; i++) {
      others.Add(upperBounds[i]);
    }
    return others;
  }

  public virtual bool IsCompilable(Type boundVariableType) =>
    ExpressionTester.IsTypeTestCompilable(boundVariableType.NormalizeToAncestorType(), boundVariableType);

  public abstract BoundedPool Clone(Cloner cloner);
}