//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

namespace Microsoft.Dafny;

public class SubSetBoundedPool(Expression set, bool isFiniteCollection) : BoundedPool {
  public readonly Expression UpperBound = set;
  public readonly bool IsFiniteCollection = isFiniteCollection;

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
