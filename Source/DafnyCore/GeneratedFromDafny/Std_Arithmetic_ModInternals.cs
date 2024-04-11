// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;

namespace Std.Arithmetic.ModInternals {

  public partial class __default {
    public static BigInteger ModRecursive(BigInteger x, BigInteger d)
    {
    TAIL_CALL_START: ;
      if ((x).Sign == -1) {
        BigInteger _in34 = (d) + (x);
        BigInteger _in35 = d;
        x = _in34;
        d = _in35;
        goto TAIL_CALL_START;
      } else if ((x) < (d)) {
        return x;
      } else {
        BigInteger _in36 = (x) - (d);
        BigInteger _in37 = d;
        x = _in36;
        d = _in37;
        goto TAIL_CALL_START;
      }
    }
  }
} // end of namespace Std.Arithmetic.ModInternals