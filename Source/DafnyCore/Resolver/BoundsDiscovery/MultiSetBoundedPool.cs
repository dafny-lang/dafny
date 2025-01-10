//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class MultiSetBoundedPool : CollectionBoundedPool {
  public readonly Expression MultiSet;

  public MultiSetBoundedPool(Expression multiset, Type bvType, Type collectionElementType)
    : base(bvType, collectionElementType, true) {
    Contract.Requires(multiset != null);
    Contract.Requires(bvType != null);
    Contract.Requires(collectionElementType != null);
    MultiSet = multiset;
  }

  public override BoundedPool Clone(Cloner cloner) {
    return new MultiSetBoundedPool(cloner.CloneExpr(MultiSet), BoundVariableType, CollectionElementType);
  }
}
