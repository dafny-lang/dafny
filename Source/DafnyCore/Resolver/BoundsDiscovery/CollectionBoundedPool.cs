//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public abstract class CollectionBoundedPool : BoundedPool {
  public readonly Type BoundVariableType;
  public readonly Type CollectionElementType;
  public readonly bool IsFiniteCollection;

  public CollectionBoundedPool(Type bvType, Type collectionElementType, bool isFiniteCollection) {
    Contract.Requires(bvType != null);
    Contract.Requires(collectionElementType != null);

    BoundVariableType = bvType;
    CollectionElementType = collectionElementType;
    IsFiniteCollection = isFiniteCollection;
  }

  public override PoolVirtues Virtues {
    get {
      var v = PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc | PoolVirtues.Enumerable;
      if (IsFiniteCollection) {
        v |= PoolVirtues.Finite;
      }
      return v;
    }
  }
  public override int Preference() => 10;
  public override bool IsCompilable(Type boundVariableType) {
    Contract.Assert(boundVariableType.Equals(BoundVariableType));
    return ExpressionTester.IsTypeTestCompilable(CollectionElementType, BoundVariableType);
  }

}
