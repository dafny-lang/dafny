//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class IntBoundedPool : BoundedPool {
  /// <summary>
  /// The bounds on each side that could not be compared statically. The compiled range starts at the largest of the
  /// lower bounds and ends at the smallest of the upper bounds.
  /// </summary>
  public readonly IReadOnlyList<Expression> LowerBounds;
  public readonly IReadOnlyList<Expression> UpperBounds;

  public IntBoundedPool(IReadOnlyList<Expression> lowerBounds, IReadOnlyList<Expression> upperBounds) {
    Contract.Requires(lowerBounds.Count != 0 || upperBounds.Count != 0);
    LowerBounds = lowerBounds;
    UpperBounds = upperBounds;
  }

  public Expression LowerBound => LowerBounds.FirstOrDefault();
  public Expression UpperBound => UpperBounds.FirstOrDefault();

  public override PoolVirtues Virtues {
    get {
      if (LowerBound != null && UpperBound != null) {
        return PoolVirtues.Finite | PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
      } else {
        return PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
      }
    }
  }
  public override int Preference() => LowerBound != null && UpperBound != null ? 5 : 4;

  public override BoundedPool Clone(Cloner cloner) {
    return new IntBoundedPool(LowerBounds.Select(cloner.CloneExpr).ToList(), UpperBounds.Select(cloner.CloneExpr).ToList());
  }
}
