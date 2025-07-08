//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class SetBoundedPool : CollectionBoundedPool {
  public readonly Expression Set;

  public SetBoundedPool(Expression set, Type bvType, Type collectionElementType, bool isFiniteCollection)
    : base(bvType, collectionElementType, isFiniteCollection) {
    Contract.Requires(set != null);
    Contract.Requires(bvType != null);
    Contract.Requires(collectionElementType != null);
    Set = set;
  }

  public override BoundedPool Clone(Cloner cloner) {
    return new SetBoundedPool(cloner.CloneExpr(Set), BoundVariableType, CollectionElementType, IsFiniteCollection);
  }
}
