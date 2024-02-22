//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

namespace Microsoft.Dafny;

public class CharBoundedPool : BoundedPool {
  public override PoolVirtues Virtues =>
    PoolVirtues.Finite | PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
  public override int Preference() => 5;
  public override BoundedPool Clone(Cloner cloner) {
    return this;
  }
}
