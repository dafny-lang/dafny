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

namespace Std.Arithmetic.Power {

  public partial class __default {
    public static BigInteger Pow(BigInteger b, BigInteger e)
    {
      BigInteger _0___accumulator = BigInteger.One;
    TAIL_CALL_START: ;
      if ((e).Sign == 0) {
        return (BigInteger.One) * (_0___accumulator);
      } else {
        _0___accumulator = (_0___accumulator) * (b);
        BigInteger _in0 = b;
        BigInteger _in1 = (e) - (BigInteger.One);
        b = _in0;
        e = _in1;
        goto TAIL_CALL_START;
      }
    }
  }
} // end of namespace Std.Arithmetic.Power