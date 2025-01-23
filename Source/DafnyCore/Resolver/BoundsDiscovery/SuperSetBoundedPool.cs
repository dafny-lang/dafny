//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

namespace Microsoft.Dafny;

public class SuperSetBoundedPool(Expression set) : BoundedPool {
  public readonly Expression LowerBound = set;
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
