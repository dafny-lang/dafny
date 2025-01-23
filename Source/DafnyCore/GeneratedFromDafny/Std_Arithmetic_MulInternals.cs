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

namespace Std.Arithmetic.MulInternals {

  public partial class __default {
    public static BigInteger MulPos(BigInteger x, BigInteger y)
    {
      BigInteger _0___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((x).Sign == 0) {
        return (BigInteger.Zero) + (_0___accumulator);
      } else {
        _0___accumulator = (_0___accumulator) + (y);
        BigInteger _in0 = (x) - (BigInteger.One);
        BigInteger _in1 = y;
        x = _in0;
        y = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger MulRecursive(BigInteger x, BigInteger y)
    {
      if ((x).Sign != -1) {
        return Std.Arithmetic.MulInternals.__default.MulPos(x, y);
      } else {
        return (new BigInteger(-1)) * (Std.Arithmetic.MulInternals.__default.MulPos((new BigInteger(-1)) * (x), y));
      }
    }
  }
} // end of namespace Std.Arithmetic.MulInternals