//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Numerics;
using System.Diagnostics.Contracts;
namespace Microsoft.Dafny {
  class ConstantFolder {
    /// <summary>
    /// Returns the largest value that can be stored in bitvector type "t".
    /// </summary>
    public static BigInteger MaxBV(Type t) {
      Contract.Requires(t != null);
      Contract.Requires(t.IsBitVectorType);
      return MaxBV(t.AsBitVectorType.Width);
    }

    /// <summary>
    /// Returns the largest value that can be stored in bitvector type of "bits" width.
    /// </summary>
    public static BigInteger MaxBV(int bits) {
      Contract.Requires(0 <= bits);
      return BigInteger.Pow(new BigInteger(2), bits) - BigInteger.One;
    }

    // Returns null if the argument is a constrained newtype (recursively)
    // Returns the transitive base type if the argument is recursively unconstrained
    public static Type AsUnconstrainedType(Type t) {
      while (true) {
        if (t.AsNewtype == null) {
          return t;
        }

        if (t.AsNewtype.Constraint != null) {
          return null;
        }

        t = t.AsNewtype.BaseType;
      }
    }

  }
}
