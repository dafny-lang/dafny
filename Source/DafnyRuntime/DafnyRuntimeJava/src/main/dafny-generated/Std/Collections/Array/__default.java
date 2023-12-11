// Class __default
// Dafny class __default compiled into Java
package Std.Collections.Array;

import Std.Wrappers.*;
import Std.BoundedInts.*;
import Std.Base64.*;
import Std.Math.*;
import Std.Collections.Seq.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static <__T> Std.Wrappers.Option<java.math.BigInteger> BinarySearch(dafny.TypeDescriptor<__T> _td___T, java.lang.Object a, __T key, dafny.Function2<__T, __T, Boolean> less)
  {
    Std.Wrappers.Option<java.math.BigInteger> r = Std.Wrappers.Option.<java.math.BigInteger>Default(_System.nat._typeDescriptor());
    java.math.BigInteger _98_lo = java.math.BigInteger.ZERO;
    java.math.BigInteger _99_hi = java.math.BigInteger.ZERO;
    java.math.BigInteger _rhs0 = java.math.BigInteger.ZERO;
    java.math.BigInteger _rhs1 = java.math.BigInteger.valueOf(java.lang.reflect.Array.getLength((a)));
    _98_lo = _rhs0;
    _99_hi = _rhs1;
    while ((_98_lo).compareTo(_99_hi) < 0) {
      java.math.BigInteger _100_mid = java.math.BigInteger.ZERO;
      _100_mid = dafny.DafnyEuclidean.EuclideanDivision((_98_lo).add(_99_hi), java.math.BigInteger.valueOf(2L));
      if (((boolean)(java.lang.Object)((less).apply(key, _td___T.getArrayElement((a), (dafny.Helpers.toInt((_100_mid)))))))) {
        _99_hi = _100_mid;
      } else if (((boolean)(java.lang.Object)((less).apply(_td___T.getArrayElement((a), (dafny.Helpers.toInt((_100_mid)))), key)))) {
        _98_lo = (_100_mid).add(java.math.BigInteger.ONE);
      } else {
        r = Std.Wrappers.Option.<java.math.BigInteger>create_Some(dafny.TypeDescriptor.BIG_INTEGER, _100_mid);
        return r;
      }
    }
    r = Std.Wrappers.Option.<java.math.BigInteger>create_None(_System.nat._typeDescriptor());
    return r;
  }
  @Override
  public java.lang.String toString() {
    return "Std.Collections.Array._default";
  }
}
