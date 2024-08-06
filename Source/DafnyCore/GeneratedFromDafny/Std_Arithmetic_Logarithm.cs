// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;

namespace Std.Arithmetic.Logarithm {

  public partial class __default {
    public static BigInteger Log(BigInteger @base, BigInteger pow)
    {
      BigInteger _138___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((pow) < (@base)) {
        return (BigInteger.Zero) + (_138___accumulator);
      } else {
        _138___accumulator = (_138___accumulator) + (BigInteger.One);
        BigInteger _in44 = @base;
        BigInteger _in45 = Dafny.Helpers.EuclideanDivision(pow, @base);
        @base = _in44;
        pow = _in45;
        goto TAIL_CALL_START;
      }
    }
  }
} // end of namespace Std.Arithmetic.Logarithm