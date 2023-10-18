using System.Numerics;

namespace Library {
  public partial class Class {
    private readonly BigInteger n;

    public Class(BigInteger n) {
      this.n = n;
    }

    public static void SayHi() {
      System.Console.WriteLine("Hello!");
    }

    public BigInteger Get() {
      return n;
    }
  }
}
