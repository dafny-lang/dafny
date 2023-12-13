// Class __default
// Dafny class __default compiled into Java
package Std.Collections.Set;

import JavaInternal.*;
import Std.Wrappers.*;
import Std.FileIOInternalExterns.*;
import Std.BoundedInts.*;
import Std.Base64.*;
import Std.Math.*;
import Std.Collections.Seq.*;
import Std.Collections.Array.*;
import Std.Collections.Imap.*;
import Std.Collections.Map.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static <__T> __T ExtractFromSingleton(dafny.TypeDescriptor<__T> _td___T, dafny.DafnySet<? extends __T> s)
  {
    return ((java.util.function.Function<java.math.BigInteger, __T>)((_let_dummy_0) -> {
      @SuppressWarnings({"unchecked", "deprecation"})
      __T _125_x = null;
      goto__ASSIGN_SUCH_THAT_1: {
        for (__T _assign_such_that_1_boxed0 : (s).Elements()) {
          __T _assign_such_that_1 = ((__T)(java.lang.Object)(_assign_such_that_1_boxed0));
          if (true) {
            _125_x = (__T)_assign_such_that_1;
            if ((s).<__T>contains(_125_x)) {
              break goto__ASSIGN_SUCH_THAT_1;
            }
          }
        }
        throw new IllegalArgumentException("assign-such-that search produced no value (line 7408)");
      }
      return _125_x;
    })).apply(java.math.BigInteger.valueOf(0));
  }
  public static <__X, __Y> dafny.DafnySet<? extends __Y> Map(dafny.TypeDescriptor<__X> _td___X, dafny.TypeDescriptor<__Y> _td___Y, java.util.function.Function<__X, __Y> f, dafny.DafnySet<? extends __X> xs)
  {
    dafny.DafnySet<? extends __Y> _126_ys = ((dafny.Function2<dafny.DafnySet<? extends __X>, java.util.function.Function<__X, __Y>, dafny.DafnySet<? extends __Y>>)(_127_xs, _128_f) -> ((dafny.Function0<dafny.DafnySet<? extends __Y>>)(() -> {
      java.util.ArrayList<__Y> _coll4 = new java.util.ArrayList<>();
      for (__X _compr_4_boxed0 : (_127_xs).Elements()) {
        __X _compr_4 = ((__X)(java.lang.Object)(_compr_4_boxed0));
        if (true) {
          __X _129_x = (__X)_compr_4;
          if ((_127_xs).<__X>contains(_129_x)) {
            _coll4.add(((__Y)(java.lang.Object)((_128_f).apply(_129_x))));
          }
        }
      }
      return new dafny.DafnySet<__Y>(_coll4);
    })).apply()).apply(xs, f);
    return _126_ys;
  }
  public static <__X> dafny.DafnySet<? extends __X> Filter(dafny.TypeDescriptor<__X> _td___X, java.util.function.Function<__X, Boolean> f, dafny.DafnySet<? extends __X> xs)
  {
    dafny.DafnySet<? extends __X> _130_ys = ((dafny.Function2<dafny.DafnySet<? extends __X>, java.util.function.Function<__X, Boolean>, dafny.DafnySet<? extends __X>>)(_131_xs, _132_f) -> ((dafny.Function0<dafny.DafnySet<? extends __X>>)(() -> {
      java.util.ArrayList<__X> _coll5 = new java.util.ArrayList<>();
      for (__X _compr_5_boxed0 : (_131_xs).Elements()) {
        __X _compr_5 = ((__X)(java.lang.Object)(_compr_5_boxed0));
        if (true) {
          __X _133_x = (__X)_compr_5;
          if (((_131_xs).<__X>contains(_133_x)) && (((boolean)(java.lang.Object)((_132_f).apply(_133_x))))) {
            _coll5.add(_133_x);
          }
        }
      }
      return new dafny.DafnySet<__X>(_coll5);
    })).apply()).apply(xs, f);
    return _130_ys;
  }
  public static dafny.DafnySet<? extends java.math.BigInteger> SetRange(java.math.BigInteger a, java.math.BigInteger b)
  {
    dafny.DafnySet<? extends java.math.BigInteger> _134___accumulator = dafny.DafnySet.<java.math.BigInteger> empty();
    TAIL_CALL_START: while (true) {
      if (java.util.Objects.equals(a, b)) {
        return dafny.DafnySet.<java.math.BigInteger>union(dafny.DafnySet.<java.math.BigInteger> empty(), _134___accumulator);
      } else {
        _134___accumulator = dafny.DafnySet.<java.math.BigInteger>union(_134___accumulator, dafny.DafnySet.<java.math.BigInteger> of(a));
        java.math.BigInteger _in30 = (a).add(java.math.BigInteger.ONE);
        java.math.BigInteger _in31 = b;
        a = _in30;
        b = _in31;
        continue TAIL_CALL_START;
      }
    }
  }
  public static dafny.DafnySet<? extends java.math.BigInteger> SetRangeZeroBound(java.math.BigInteger n) {
    return __default.SetRange(java.math.BigInteger.ZERO, n);
  }
  @Override
  public java.lang.String toString() {
    return "Std.Collections.Set._default";
  }
}
