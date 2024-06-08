// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;

namespace Std.Arithmetic.DivInternals {

  public partial class __default {
    public static BigInteger DivPos(BigInteger x, BigInteger d)
    {
      BigInteger _136___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((x).Sign == -1) {
        _136___accumulator = (_136___accumulator) + (new BigInteger(-1));
        BigInteger _in38 = (x) + (d);
        BigInteger _in39 = d;
        x = _in38;
        d = _in39;
        goto TAIL_CALL_START;
      } else if ((x) < (d)) {
        return (BigInteger.Zero) + (_136___accumulator);
      } else {
        _136___accumulator = (_136___accumulator) + (BigInteger.One);
        BigInteger _in40 = (x) - (d);
        BigInteger _in41 = d;
        x = _in40;
        d = _in41;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger DivRecursive(BigInteger x, BigInteger d)
    {
      if ((d).Sign == 1) {
        return Std.Arithmetic.DivInternals.__default.DivPos(x, d);
      } else {
        return (new BigInteger(-1)) * (Std.Arithmetic.DivInternals.__default.DivPos(x, (new BigInteger(-1)) * (d)));
      }
    }
  }
} // end of namespace Std.Arithmetic.DivInternals