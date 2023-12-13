// Class uint64
// Dafny class uint64 compiled into Java
package Std.BoundedInts;

import JavaInternal.*;
import Std.Wrappers.*;
import Std.FileIOInternalExterns.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class uint64 {
  public uint64() {
  }
  public static java.util.ArrayList<java.lang.Long> IntegerRange(java.math.BigInteger lo, java.math.BigInteger hi) {
    java.util.ArrayList<java.lang.Long> arr = new java.util.ArrayList<>();
    for (java.math.BigInteger j = lo; j.compareTo(hi) < 0; j = j.add(java.math.BigInteger.ONE)) { arr.add(java.lang.Long.valueOf(j.longValue())); }
    return arr;
  }
  private static final dafny.TypeDescriptor<java.lang.Long> _TYPE = dafny.TypeDescriptor.longWithDefault(0L);
  public static dafny.TypeDescriptor<java.lang.Long> _typeDescriptor() {
    return (dafny.TypeDescriptor<java.lang.Long>) (dafny.TypeDescriptor<?>) _TYPE;
  }
}
