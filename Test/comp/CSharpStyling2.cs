using System.Numerics;

namespace _module {
  public partial class MyClass {
    public MyClass() { }  // needed by Dafny in order to call constructor "Init"
    public MyClass(BigInteger x) {
      this.u = x;
    }
    public MyClass(bool y) {
      this.u = y ? 3 : -3;
    }

    public BigInteger OneResultExtern(BigInteger z) {
      BigInteger r = 12;
      if (z == 0) {
        r = 8;
        return r;
      } else if (z == 1) {
        r = 10;
        return r;
      }
      return r;
    }
    
    public void TwoResultsExtern(BigInteger z, out BigInteger r, out BigInteger s) {
      if (z == 0) {
        r = 5;
        s = 7;
        return;
      } else {
        r = 9;
        s = 11;
      }
      return;
    }
  }
}
