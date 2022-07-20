// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Numerics;
using System.Globalization;

namespace Microsoft.Dafny {
  internal static class BigIntegerParser {
    /// <summary>
    ///   Mono does not support the BigInteger.TryParse method. In practice,
    ///   we seldom actually need to parse huge integers, so it makes sense
    ///   to support most real-life cases by simply trying to parse using
    ///   Int64, and only falling back if needed.
    /// </summary>
    internal static BigInteger Parse(string str, NumberStyles style) {
      UInt64 parsed;
      if (UInt64.TryParse(str, style, NumberFormatInfo.CurrentInfo, out parsed)) {
        return new BigInteger(parsed);
      } else {
        // Throws on Mono 3.2.8
        return BigInteger.Parse(str, style);
      }
    }

    internal static BigInteger Parse(string str) {
      return BigIntegerParser.Parse(str, NumberStyles.Integer);
    }
  }
}
