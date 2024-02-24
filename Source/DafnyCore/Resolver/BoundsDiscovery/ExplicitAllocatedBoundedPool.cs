//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

namespace Microsoft.Dafny;

public class ExplicitAllocatedBoundedPool : BoundedPool {
  public ExplicitAllocatedBoundedPool() {
  }
  public override PoolVirtues Virtues => PoolVirtues.Finite | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
  public override int Preference() => 0;
  public override BoundedPool Clone(Cloner cloner) {
    return this;
  }
}
