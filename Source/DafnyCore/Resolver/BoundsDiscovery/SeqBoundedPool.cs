//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class SeqBoundedPool : CollectionBoundedPool {
  public readonly Expression Seq;

  public SeqBoundedPool(Expression seq, Type bvType, Type collectionElementType)
    : base(bvType, collectionElementType, true) {
    Contract.Requires(seq != null);
    Contract.Requires(bvType != null);
    Contract.Requires(collectionElementType != null);
    Seq = seq;
  }

  public override BoundedPool Clone(Cloner cloner) {
    return new SeqBoundedPool(cloner.CloneExpr(Seq), BoundVariableType, CollectionElementType);
  }
}
