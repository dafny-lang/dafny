// Class __default
// Dafny class __default compiled into Java
package Std.Math;

import Std.Wrappers.*;
import Std.BoundedInts.*;
import Std.Base64.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static java.math.BigInteger Min(java.math.BigInteger a, java.math.BigInteger b)
  {
    if ((a).compareTo(b) < 0) {
      return a;
    } else {
      return b;
    }
  }
  public static java.math.BigInteger Min3(java.math.BigInteger a, java.math.BigInteger b, java.math.BigInteger c)
  {
    return __default.Min(a, __default.Min(b, c));
  }
  public static java.math.BigInteger Max(java.math.BigInteger a, java.math.BigInteger b)
  {
    if ((a).compareTo(b) < 0) {
      return b;
    } else {
      return a;
    }
  }
  public static java.math.BigInteger Max3(java.math.BigInteger a, java.math.BigInteger b, java.math.BigInteger c)
  {
    return __default.Max(a, __default.Max(b, c));
  }
  public static java.math.BigInteger Abs(java.math.BigInteger a) {
    if ((a).signum() == -1) {
      return (java.math.BigInteger.ZERO).subtract(a);
    } else {
      return a;
    }
  }
  @Override
  public java.lang.String toString() {
    return "Std.Math._default";
  }
}
