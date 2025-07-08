//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

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
