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
    java.math.BigInteger _108_lo = java.math.BigInteger.ZERO;
    java.math.BigInteger _109_hi = java.math.BigInteger.ZERO;
    java.math.BigInteger _rhs0 = java.math.BigInteger.ZERO;
    java.math.BigInteger _rhs1 = java.math.BigInteger.valueOf(java.lang.reflect.Array.getLength((a)));
    _108_lo = _rhs0;
    _109_hi = _rhs1;
    while ((_108_lo).compareTo(_109_hi) < 0) {
      java.math.BigInteger _110_mid = java.math.BigInteger.ZERO;
      _110_mid = dafny.DafnyEuclidean.EuclideanDivision((_108_lo).add(_109_hi), java.math.BigInteger.valueOf(2L));
      if (((boolean)(java.lang.Object)((less).apply(key, _td___T.getArrayElement((a), (dafny.Helpers.toInt((_110_mid)))))))) {
        _109_hi = _110_mid;
      } else if (((boolean)(java.lang.Object)((less).apply(_td___T.getArrayElement((a), (dafny.Helpers.toInt((_110_mid)))), key)))) {
        _108_lo = (_110_mid).add(java.math.BigInteger.ONE);
      } else {
        r = Std.Wrappers.Option.<java.math.BigInteger>create_Some(dafny.TypeDescriptor.BIG_INTEGER, _110_mid);
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
