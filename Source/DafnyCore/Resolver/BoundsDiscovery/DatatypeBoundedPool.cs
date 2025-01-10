//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class DatatypeBoundedPool : BoundedPool {
  public readonly DatatypeDecl Decl;

  public DatatypeBoundedPool(DatatypeDecl d) {
    Contract.Requires(d != null);
    Decl = d;
  }
  public override PoolVirtues Virtues =>
    PoolVirtues.Finite | PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
  public override int Preference() => 8;
  public override BoundedPool Clone(Cloner cloner) {
    return this;
  }
}
