// Class nat16
// Dafny class nat16 compiled into Java
package Std.BoundedInts;

import JavaInternal.*;
import Std.Wrappers.*;
import Std.FileIOInternalExterns.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class nat16 {
  public nat16() {
  }
  public static java.util.ArrayList<java.lang.Short> IntegerRange(java.math.BigInteger lo, java.math.BigInteger hi) {
    java.util.ArrayList<java.lang.Short> arr = new java.util.ArrayList<>();
    for (java.math.BigInteger j = lo; j.compareTo(hi) < 0; j = j.add(java.math.BigInteger.ONE)) { arr.add(java.lang.Short.valueOf(j.shortValue())); }
    return arr;
  }
  private static final dafny.TypeDescriptor<java.lang.Short> _TYPE = dafny.TypeDescriptor.shortWithDefault((short)0);
  public static dafny.TypeDescriptor<java.lang.Short> _typeDescriptor() {
    return (dafny.TypeDescriptor<java.lang.Short>) (dafny.TypeDescriptor<?>) _TYPE;
  }
}
