// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in .NET should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
#pragma warning disable CS0164 // This label has not been referenced
#pragma warning disable CS0162 // Unreachable code detected
#pragma warning disable CS1717 // Assignment made to same variable

namespace Std.Math {

  public partial class __default {
    public static BigInteger Min(BigInteger a, BigInteger b)
    {
      if ((a) < (b)) {
        return a;
      } else {
        return b;
      }
    }
    public static BigInteger Min3(BigInteger a, BigInteger b, BigInteger c)
    {
      return Std.Math.__default.Min(a, Std.Math.__default.Min(b, c));
    }
    public static BigInteger Max(BigInteger a, BigInteger b)
    {
      if ((a) < (b)) {
        return b;
      } else {
        return a;
      }
    }
    public static BigInteger Max3(BigInteger a, BigInteger b, BigInteger c)
    {
      return Std.Math.__default.Max(a, Std.Math.__default.Max(b, c));
    }
    public static BigInteger Abs(BigInteger a) {
      if ((a).Sign == -1) {
        return (BigInteger.Zero) - (a);
      } else {
        return a;
      }
    }
  }
} // end of namespace Std.Math