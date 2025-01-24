//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

namespace Microsoft.Dafny;

public class DatatypeInclusionBoundedPool : BoundedPool {
  public readonly bool IsIndDatatype;

  public DatatypeInclusionBoundedPool(bool isIndDatatype) : base() {
    IsIndDatatype = isIndDatatype;
  }

  public override PoolVirtues Virtues =>
    (IsIndDatatype ? PoolVirtues.Finite : PoolVirtues.None) | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
  public override int Preference() => 2;
  public override BoundedPool Clone(Cloner cloner) {
    return this;
  }
}
