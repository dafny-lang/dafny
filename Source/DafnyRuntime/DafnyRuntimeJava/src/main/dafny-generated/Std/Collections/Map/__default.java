// Class __default
// Dafny class __default compiled into Java
package Std.Collections.Map;

import Std.Wrappers.*;
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
    return ((java.util.function.Function<dafny.DafnyMap<? extends __X, ? extends __Y>, dafny.DafnyMap<? extends __X, ? extends __Y>>)(_111_m) -> ((dafny.Function0<dafny.DafnyMap<? extends __X, ? extends __Y>>)(() -> {
      java.util.HashMap<__X, __Y> _coll1 = new java.util.HashMap<>();
      for (__X _compr_1_boxed0 : (_111_m).keySet().Elements()) {
        __X _compr_1 = ((__X)(java.lang.Object)(_compr_1_boxed0));
        if (true) {
          __X _112_x = (__X)_compr_1;
          if ((_111_m).<__X>contains(_112_x)) {
            _coll1.put(_112_x,((__Y)(java.lang.Object)((_111_m).get(_112_x))));
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
    dafny.DafnyMap<? extends __X, ? extends __Y> _113_m_k = ((dafny.Function2<dafny.DafnyMap<? extends __X, ? extends __Y>, __X, dafny.DafnyMap<? extends __X, ? extends __Y>>)(_114_m, _115_x) -> ((dafny.Function0<dafny.DafnyMap<? extends __X, ? extends __Y>>)(() -> {
      java.util.HashMap<__X, __Y> _coll2 = new java.util.HashMap<>();
      for (__X _compr_2_boxed0 : (_114_m).keySet().Elements()) {
        __X _compr_2 = ((__X)(java.lang.Object)(_compr_2_boxed0));
        if (true) {
          __X _116_x_k = (__X)_compr_2;
          if (((_114_m).<__X>contains(_116_x_k)) && (!java.util.Objects.equals(_116_x_k, _115_x))) {
            _coll2.put(_116_x_k,((__Y)(java.lang.Object)((_114_m).get(_116_x_k))));
          }
        }
      }
      return new dafny.DafnyMap<__X,__Y>(_coll2);
    })).apply()).apply(m, x);
    return _113_m_k;
  }
  public static <__X, __Y> dafny.DafnyMap<? extends __X, ? extends __Y> Restrict(dafny.TypeDescriptor<__X> _td___X, dafny.TypeDescriptor<__Y> _td___Y, dafny.DafnyMap<? extends __X, ? extends __Y> m, dafny.DafnySet<? extends __X> xs)
  {
    return ((dafny.Function2<dafny.DafnySet<? extends __X>, dafny.DafnyMap<? extends __X, ? extends __Y>, dafny.DafnyMap<? extends __X, ? extends __Y>>)(_117_xs, _118_m) -> ((dafny.Function0<dafny.DafnyMap<? extends __X, ? extends __Y>>)(() -> {
      java.util.HashMap<__X, __Y> _coll3 = new java.util.HashMap<>();
      for (__X _compr_3_boxed0 : (_117_xs).Elements()) {
        __X _compr_3 = ((__X)(java.lang.Object)(_compr_3_boxed0));
        if (true) {
          __X _119_x = (__X)_compr_3;
          if (((_117_xs).<__X>contains(_119_x)) && ((_118_m).<__X>contains(_119_x))) {
            _coll3.put(_119_x,((__Y)(java.lang.Object)((_118_m).get(_119_x))));
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
