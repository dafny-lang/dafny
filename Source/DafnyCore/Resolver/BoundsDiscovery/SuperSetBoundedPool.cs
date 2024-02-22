//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

namespace Microsoft.Dafny;

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
