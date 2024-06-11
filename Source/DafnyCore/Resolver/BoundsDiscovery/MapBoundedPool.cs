//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class MapBoundedPool : CollectionBoundedPool {
  public readonly Expression Map;

  public MapBoundedPool(Expression map, Type bvType, Type collectionElementType, bool isFiniteCollection)
    : base(bvType, collectionElementType, isFiniteCollection) {
    Contract.Requires(map != null);
    Contract.Requires(bvType != null);
    Contract.Requires(collectionElementType != null);
    Map = map;
  }
  public override BoundedPool Clone(Cloner cloner) {
    return new MapBoundedPool(cloner.CloneExpr(Map), BoundVariableType, CollectionElementType, IsFiniteCollection);
  }
}
