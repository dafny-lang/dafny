
using System.Numerics;

namespace Interop {

  public static partial class __default {
    public static BigInteger Int32ToInt(int value) {
      return new BigInteger(value);
    }
    public static Std.Wrappers._IOption<int> IntToInt32(BigInteger value) {
      if (value > int.MaxValue || value < int.MinValue) {
        return Std.Wrappers.Option<int>.create_None();
      }
      else
      {
        return Std.Wrappers.Option<int>.create_Some((int)value);
      }
    }
  }
}