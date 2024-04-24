//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class ExactBoundedPool : BoundedPool {
  public readonly Expression E;
  public ExactBoundedPool(Expression e) {
    Contract.Requires(e != null);
    E = e;
  }
  public override PoolVirtues Virtues =>
    PoolVirtues.Finite | PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
  public override int Preference() => 15;  // the best of all bounds

  public override BoundedPool Clone(Cloner cloner) {
    return new ExactBoundedPool(cloner.CloneExpr(E));
  }
}
