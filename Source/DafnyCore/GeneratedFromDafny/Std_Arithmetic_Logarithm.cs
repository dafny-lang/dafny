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

namespace Std.Arithmetic.Logarithm {

  public partial class __default {
    public static BigInteger Log(BigInteger @base, BigInteger pow)
    {
      BigInteger _0___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((pow) < (@base)) {
        return (BigInteger.Zero) + (_0___accumulator);
      } else {
        _0___accumulator = (_0___accumulator) + (BigInteger.One);
        BigInteger _in0 = @base;
        BigInteger _in1 = Dafny.Helpers.EuclideanDivision(pow, @base);
        @base = _in0;
        pow = _in1;
        goto TAIL_CALL_START;
      }
    }
  }
} // end of namespace Std.Arithmetic.Logarithm