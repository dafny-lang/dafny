// Class __default
// Dafny class __default compiled into Java
package Std.Collections.Map;

import JavaInternal.*;
import Std.Wrappers.*;
import Std.FileIOInternalExterns.*;
import Std.BoundedInts.*;
import Std.Base64.*;
import Std.Math.*;
import Std.Collections.Seq.*;
import Std.Collections.Array.*;
import Std.Collections.Imap.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static <__X, __Y> Std.Wrappers.Option<__Y> Get(dafny.TypeDescriptor<__X> _td___X, dafny.TypeDescriptor<__Y> _td___Y, dafny.DafnyMap<? extends __X, ? extends __Y> m, __X x)
  {
    if ((m).<__X>contains(x)) {
      return Std.Wrappers.Option.<__Y>create_Some(_td___Y, ((__Y)(java.lang.Object)((m).get(x))));
    } else {
      return Std.Wrappers.Option.<__Y>create_None(_td___Y);
    }
  }
  public static <__X, __Y> dafny.DafnyMap<? extends __X, ? extends __Y> ToImap(dafny.TypeDescriptor<__X> _td___X, dafny.TypeDescriptor<__Y> _td___Y, dafny.DafnyMap<? extends __X, ? extends __Y> m)
  {
    return ((java.util.function.Function<dafny.DafnyMap<? extends __X, ? extends __Y>, dafny.DafnyMap<? extends __X, ? extends __Y>>)(_116_m) -> ((dafny.Function0<dafny.DafnyMap<? extends __X, ? extends __Y>>)(() -> {
      java.util.HashMap<__X, __Y> _coll1 = new java.util.HashMap<>();
      for (__X _compr_1_boxed0 : (_116_m).keySet().Elements()) {
        __X _compr_1 = ((__X)(java.lang.Object)(_compr_1_boxed0));
        if (true) {
          __X _117_x = (__X)_compr_1;
          if ((_116_m).<__X>contains(_117_x)) {
            _coll1.put(_117_x,((__Y)(java.lang.Object)((_116_m).get(_117_x))));
          }
        }
      }
      return new dafny.DafnyMap<__X,__Y>(_coll1);
    })).apply()).apply(m);
  }
  public static <__X, __Y> dafny.DafnyMap<? extends __X, ? extends __Y> RemoveKeys(dafny.TypeDescriptor<__X> _td___X, dafny.TypeDescriptor<__Y> _td___Y, dafny.DafnyMap<? extends __X, ? extends __Y> m, dafny.DafnySet<? extends __X> xs)
  {
    return dafny.DafnyMap.<__X, __Y>subtract(m, xs);
  }
  public static <__X, __Y> dafny.DafnyMap<? extends __X, ? extends __Y> Remove(dafny.TypeDescriptor<__X> _td___X, dafny.TypeDescriptor<__Y> _td___Y, dafny.DafnyMap<? extends __X, ? extends __Y> m, __X x)
  {
    dafny.DafnyMap<? extends __X, ? extends __Y> _118_m_k = ((dafny.Function2<dafny.DafnyMap<? extends __X, ? extends __Y>, __X, dafny.DafnyMap<? extends __X, ? extends __Y>>)(_119_m, _120_x) -> ((dafny.Function0<dafny.DafnyMap<? extends __X, ? extends __Y>>)(() -> {
      java.util.HashMap<__X, __Y> _coll2 = new java.util.HashMap<>();
      for (__X _compr_2_boxed0 : (_119_m).keySet().Elements()) {
        __X _compr_2 = ((__X)(java.lang.Object)(_compr_2_boxed0));
        if (true) {
          __X _121_x_k = (__X)_compr_2;
          if (((_119_m).<__X>contains(_121_x_k)) && (!java.util.Objects.equals(_121_x_k, _120_x))) {
            _coll2.put(_121_x_k,((__Y)(java.lang.Object)((_119_m).get(_121_x_k))));
          }
        }
      }
      return new dafny.DafnyMap<__X,__Y>(_coll2);
    })).apply()).apply(m, x);
    return _118_m_k;
  }
  public static <__X, __Y> dafny.DafnyMap<? extends __X, ? extends __Y> Restrict(dafny.TypeDescriptor<__X> _td___X, dafny.TypeDescriptor<__Y> _td___Y, dafny.DafnyMap<? extends __X, ? extends __Y> m, dafny.DafnySet<? extends __X> xs)
  {
    return ((dafny.Function2<dafny.DafnySet<? extends __X>, dafny.DafnyMap<? extends __X, ? extends __Y>, dafny.DafnyMap<? extends __X, ? extends __Y>>)(_122_xs, _123_m) -> ((dafny.Function0<dafny.DafnyMap<? extends __X, ? extends __Y>>)(() -> {
      java.util.HashMap<__X, __Y> _coll3 = new java.util.HashMap<>();
      for (__X _compr_3_boxed0 : (_122_xs).Elements()) {
        __X _compr_3 = ((__X)(java.lang.Object)(_compr_3_boxed0));
        if (true) {
          __X _124_x = (__X)_compr_3;
          if (((_122_xs).<__X>contains(_124_x)) && ((_123_m).<__X>contains(_124_x))) {
            _coll3.put(_124_x,((__Y)(java.lang.Object)((_123_m).get(_124_x))));
          }
        }
      }
      return new dafny.DafnyMap<__X,__Y>(_coll3);
    })).apply()).apply(xs, m);
  }
  public static <__X, __Y> dafny.DafnyMap<? extends __X, ? extends __Y> Union(dafny.TypeDescriptor<__X> _td___X, dafny.TypeDescriptor<__Y> _td___Y, dafny.DafnyMap<? extends __X, ? extends __Y> m, dafny.DafnyMap<? extends __X, ? extends __Y> m_k)
  {
    return dafny.DafnyMap.<__X, __Y>merge(m, m_k);
  }
  @Override
  public java.lang.String toString() {
    return "Std.Collections.Map._default";
  }
}
