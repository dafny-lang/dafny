// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;

namespace Std.Arithmetic.MulInternals {

  public partial class __default {
    public static BigInteger MulPos(BigInteger x, BigInteger y)
    {
      BigInteger _149___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((x).Sign == 0) {
        return (BigInteger.Zero) + (_149___accumulator);
      } else {
        _149___accumulator = (_149___accumulator) + (y);
        BigInteger _in32 = (x) - (BigInteger.One);
        BigInteger _in33 = y;
        x = _in32;
        y = _in33;
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