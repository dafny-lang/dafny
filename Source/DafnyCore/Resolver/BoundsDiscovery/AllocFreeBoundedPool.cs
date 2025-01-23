//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

namespace Microsoft.Dafny;

public class AllocFreeBoundedPool(Type t) : BoundedPool {
  public Type Type = t;

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
