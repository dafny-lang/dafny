// Class int8
// Dafny class int8 compiled into Java
package Std.BoundedInts;

import Std.Wrappers.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class int8 {
  public int8() {
  }
  public static java.util.ArrayList<java.lang.Byte> IntegerRange(java.math.BigInteger lo, java.math.BigInteger hi) {
    java.util.ArrayList<java.lang.Byte> arr = new java.util.ArrayList<>();
    for (java.math.BigInteger j = lo; j.compareTo(hi) < 0; j = j.add(java.math.BigInteger.ONE)) { arr.add(java.lang.Byte.valueOf(j.byteValue())); }
    return arr;
  }
  private static final dafny.TypeDescriptor<java.lang.Byte> _TYPE = dafny.TypeDescriptor.byteWithDefault((byte)0);
  public static dafny.TypeDescriptor<java.lang.Byte> _typeDescriptor() {
    return (dafny.TypeDescriptor<java.lang.Byte>) (dafny.TypeDescriptor<?>) _TYPE;
  }
}
