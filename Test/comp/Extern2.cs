using System.Numerics;

namespace Library {
  public partial class LibClass {
    // static method CallMeInt(x: int) returns (y: int, z: int)
    public static void CallMeInt(BigInteger x, out BigInteger y, out BigInteger z) {
      y = x + BigInteger.One;
      z = y + y;
    }
    // static method CallMeNative(x: MyInt, b: bool) returns (y: MyInt)
    public static void CallMeNative(int x, bool b, out int y) {
      y = b ? x + 1 : x - 1;
    }
  }
}
