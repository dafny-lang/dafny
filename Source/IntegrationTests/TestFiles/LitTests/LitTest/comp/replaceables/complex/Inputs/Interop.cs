
using System.Numerics;

namespace Interop {

  public static partial class __default {
    public static BigInteger Int32ToInt(int value) {
      return new BigInteger(value);
    }
    public static DafnyStdLibs.Wrappers._IOption<int> IntToInt32(BigInteger value) {
      if (value > int.MaxValue || value < int.MinValue) {
        return DafnyStdLibs.Wrappers.Option<int>.create_None();
      }
      else
      {
        return DafnyStdLibs.Wrappers.Option<int>.create_Some((int)value);
      }
    }
  }
}