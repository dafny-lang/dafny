using System.Numerics;

namespace Library {
  public partial class LibClass {
    // static method CallMeInt(x: int) returns (y: int, z: int)
    public static void CallMeInt(BigInteger x, out BigInteger y, out BigInteger z) {
      y = x + BigInteger.One;
      z = y + y;
    }
    // static method CallMeNative(x: MyInt, b: bool) returns (y: MyInt)
    public static int CallMeNative(int x, bool b) {
      var y = b ? x + 1 : x - 1;
      return y;
    }
  }

  class OtherClass {
    public static object CallMe() {
      return "OtherClass.CallMe";
    }
  }

  // must be partial, since Dafny will also generate some methods into this class
  public partial class Mixed {
    public static void P() {
      System.Console.WriteLine("Mixed.P");
    }
    public void IP() {
      System.Console.WriteLine("Mixed.IP");
    }
    public static BigInteger G() {
      return 1;
    }
    public BigInteger IG() {
      return 2;
    }
  }
  // It's okay for the following class to not be partial, since Dafny won't be adding
  // any members to it. In fact, this test is to make sure that Dafny does not
  // generate this class at all.
  public class AllExtern {
    public static void P() {
      System.Console.WriteLine("AllExtern.P");
    }
  }

  public partial class SingletonOptimization {
    public static int SingletonTuple(int a) {
      return a + 1;
    }
    public static int NoWrapper(int a) {
      return a + 1;
    }
    public static int GhostWrapper(int a) {
      return a + 1;
    }
  }
}
