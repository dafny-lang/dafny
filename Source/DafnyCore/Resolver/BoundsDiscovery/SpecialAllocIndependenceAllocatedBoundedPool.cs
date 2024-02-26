//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

namespace Microsoft.Dafny;

public class SpecialAllocIndependenceAllocatedBoundedPool : BoundedPool {
  public SpecialAllocIndependenceAllocatedBoundedPool() {
  }
  public override PoolVirtues Virtues => PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
  public override int Preference() => 0;
  public override BoundedPool Clone(Cloner cloner) {
    return this;
  }
}
