// Class __default
// Dafny class __default compiled into Java
package Std.Collections.Array;

import JavaInternal.*;
import Std.Wrappers.*;
import Std.FileIOInternalExterns.*;
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
    java.math.BigInteger _113_lo = java.math.BigInteger.ZERO;
    java.math.BigInteger _114_hi = java.math.BigInteger.ZERO;
    java.math.BigInteger _rhs5 = java.math.BigInteger.ZERO;
    java.math.BigInteger _rhs6 = java.math.BigInteger.valueOf(java.lang.reflect.Array.getLength((a)));
    _113_lo = _rhs5;
    _114_hi = _rhs6;
    while ((_113_lo).compareTo(_114_hi) < 0) {
      java.math.BigInteger _115_mid = java.math.BigInteger.ZERO;
      _115_mid = dafny.DafnyEuclidean.EuclideanDivision((_113_lo).add(_114_hi), java.math.BigInteger.valueOf(2L));
      if (((boolean)(java.lang.Object)((less).apply(key, _td___T.getArrayElement((a), (dafny.Helpers.toInt((_115_mid)))))))) {
        _114_hi = _115_mid;
      } else if (((boolean)(java.lang.Object)((less).apply(_td___T.getArrayElement((a), (dafny.Helpers.toInt((_115_mid)))), key)))) {
        _113_lo = (_115_mid).add(java.math.BigInteger.ONE);
      } else {
        r = Std.Wrappers.Option.<java.math.BigInteger>create_Some(dafny.TypeDescriptor.BIG_INTEGER, _115_mid);
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
