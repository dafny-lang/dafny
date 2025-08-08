using System.Numerics;

namespace _module {

  public partial class __default {
    public static BigInteger Foo(BigInteger x) {
      return BigInteger.Zero;
    }
    public static BigInteger Bar(BigInteger x) {
      return BigInteger.Zero;
    }
    public static BigInteger Baz(BigInteger x) {
      return x;
    }
    public static BigInteger NotCalled(BigInteger x) {
      return BigInteger.One;
    }
    
    public static BigInteger FunctionWithUnnamedResult(BigInteger x) {
      return x;
    }
    
    public static T GenFunction<T>(BigInteger x, T y) {
      return y;
    }
    
    public static T GenMethod<T>(BigInteger x, T y) {
      return y;
    }
  }
}
