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

namespace Std.Arithmetic.ModInternals {

  public partial class __default {
    public static BigInteger ModRecursive(BigInteger x, BigInteger d)
    {
    TAIL_CALL_START: ;
      if ((x).Sign == -1) {
        BigInteger _in0 = (d) + (x);
        BigInteger _in1 = d;
        x = _in0;
        d = _in1;
        goto TAIL_CALL_START;
      } else if ((x) < (d)) {
        return x;
      } else {
        BigInteger _in2 = (x) - (d);
        BigInteger _in3 = d;
        x = _in2;
        d = _in3;
        goto TAIL_CALL_START;
      }
    }
  }
} // end of namespace Std.Arithmetic.ModInternals