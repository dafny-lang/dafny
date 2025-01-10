// Class nat
// Dafny class nat compiled into Java
package _System;

@SuppressWarnings({"unchecked", "deprecation"})
public class nat {
  public nat() {
  }
  public static boolean _Is(java.math.BigInteger __source) {
    java.math.BigInteger _0_x = __source;
    return (_0_x).signum() != -1;
  }
  private static final dafny.TypeDescriptor<java.math.BigInteger> _TYPE = dafny.TypeDescriptor.<java.math.BigInteger>referenceWithInitializer(java.math.BigInteger.class, () -> java.math.BigInteger.ZERO);
  public static dafny.TypeDescriptor<java.math.BigInteger> _typeDescriptor() {
    return (dafny.TypeDescriptor<java.math.BigInteger>) (dafny.TypeDescriptor<?>) _TYPE;
  }
}
