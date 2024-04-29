// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;

namespace Std.Arithmetic.Power {

  public partial class __default {
    public static BigInteger Pow(BigInteger b, BigInteger e)
    {
      BigInteger _151___accumulator = BigInteger.One;
    TAIL_CALL_START: ;
      if ((e).Sign == 0) {
        return (BigInteger.One) * (_151___accumulator);
      } else {
        _151___accumulator = (_151___accumulator) * (b);
        BigInteger _in42 = b;
        BigInteger _in43 = (e) - (BigInteger.One);
        b = _in42;
        e = _in43;
        goto TAIL_CALL_START;
      }
    }
  }
} // end of namespace Std.Arithmetic.Power