module Foo {
    class A {

        const a : int
        const b : int

        constructor(k : int, j : int)
        {
            //a := k;
            //b := j;
            a, b := k, j;
        }
    }
    method Main()
    {
        var o := new A(1, 2);
    }
}

/*
public class A {
  public A() {
    this._a = java.math.BigInteger.ZERO;
    this._b = java.math.BigInteger.ZERO;
  }
  public void __ctor(java.math.BigInteger k, java.math.BigInteger j)
  {
    (this)._a = k;
    (this)._b = j;
  }
  public java.math.BigInteger _a;
  public java.math.BigInteger a()
  {
    return this._a;
  }
  public java.math.BigInteger _b;
  public java.math.BigInteger b()
  {
    return this._b;
  }
  private static final dafny.TypeDescriptor<A> _TYPE = dafny.TypeDescriptor.referenceWithInitializer(A.class, () -> (A) null);
  public static dafny.TypeDescriptor<A> _typeDescriptor() {
    return (dafny.TypeDescriptor<A>) (dafny.TypeDescriptor<?>) _TYPE;
  }
*/