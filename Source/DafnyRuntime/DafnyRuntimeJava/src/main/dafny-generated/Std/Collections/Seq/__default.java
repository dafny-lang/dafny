// Class __default
// Dafny class __default compiled into Java
package Std.Collections.Seq;

import Std.Wrappers.*;
import Std.BoundedInts.*;
import Std.Base64.*;
import Std.Math.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static <__T> __T First(dafny.TypeDescriptor<__T> _td___T, dafny.DafnySequence<? extends __T> xs)
  {
    return ((__T)(java.lang.Object)((xs).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
  }
  public static <__T> dafny.DafnySequence<? extends __T> DropFirst(dafny.TypeDescriptor<__T> _td___T, dafny.DafnySequence<? extends __T> xs)
  {
    return (xs).drop(java.math.BigInteger.ONE);
  }
  public static <__T> __T Last(dafny.TypeDescriptor<__T> _td___T, dafny.DafnySequence<? extends __T> xs)
  {
    return ((__T)(java.lang.Object)((xs).select(dafny.Helpers.toInt(((java.math.BigInteger.valueOf((xs).length())).subtract(java.math.BigInteger.ONE))))));
  }
  public static <__T> dafny.DafnySequence<? extends __T> DropLast(dafny.TypeDescriptor<__T> _td___T, dafny.DafnySequence<? extends __T> xs)
  {
    return (xs).take((java.math.BigInteger.valueOf((xs).length())).subtract(java.math.BigInteger.ONE));
  }
  public static <__T> java.lang.Object ToArray(dafny.TypeDescriptor<__T> _td___T, dafny.DafnySequence<? extends __T> xs)
  {
    java.lang.Object a = (java.lang.Object)_td___T.newArray(0);
    if(true) {
      java.util.function.Function<java.math.BigInteger, __T> _init2 = ((java.util.function.Function<dafny.DafnySequence<? extends __T>, java.util.function.Function<java.math.BigInteger, __T>>)(_70_xs) -> ((java.util.function.Function<java.math.BigInteger, __T>)(_71_i_boxed0) -> {
        java.math.BigInteger _71_i = ((java.math.BigInteger)(java.lang.Object)(_71_i_boxed0));
        return ((__T)(java.lang.Object)((_70_xs).select(dafny.Helpers.toInt((_71_i)))));
      })).apply(xs);
      java.lang.Object _nw2 = (java.lang.Object) _td___T.newArray(dafny.Helpers.toIntChecked((java.math.BigInteger.valueOf((xs).length())), "Java arrays may be no larger than the maximum 32-bit signed int"));
      for (java.math.BigInteger _i0_2 = java.math.BigInteger.ZERO; _i0_2.compareTo(java.math.BigInteger.valueOf(java.lang.reflect.Array.getLength(_nw2))) < 0; _i0_2 = _i0_2.add(java.math.BigInteger.ONE)) {
        _td___T.setArrayElement(_nw2, dafny.Helpers.toInt(_i0_2), ((__T)(java.lang.Object)(_init2.apply(_i0_2))));
      }
      a = _nw2;
    }
    return a;
  }
  public static <__T> dafny.DafnySet<? extends __T> ToSet(dafny.TypeDescriptor<__T> _td___T, dafny.DafnySequence<? extends __T> xs)
  {
    return ((java.util.function.Function<dafny.DafnySequence<? extends __T>, dafny.DafnySet<? extends __T>>)(_72_xs) -> ((dafny.Function0<dafny.DafnySet<? extends __T>>)(() -> {
      java.util.ArrayList<__T> _coll0 = new java.util.ArrayList<>();
      for (__T _compr_0_boxed0 : (_72_xs).Elements()) {
        __T _compr_0 = ((__T)(java.lang.Object)(_compr_0_boxed0));
        if (true) {
          __T _73_x = (__T)_compr_0;
          if ((_72_xs).contains(_73_x)) {
            _coll0.add(_73_x);
          }
        }
      }
      return new dafny.DafnySet<__T>(_coll0);
    })).apply()).apply(xs);
  }
  public static <__T> java.math.BigInteger IndexOf(dafny.TypeDescriptor<__T> _td___T, dafny.DafnySequence<? extends __T> xs, __T v)
  {
    java.math.BigInteger _74___accumulator = java.math.BigInteger.ZERO;
    TAIL_CALL_START: while (true) {
      if (java.util.Objects.equals(((__T)(java.lang.Object)((xs).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))), v)) {
        return (java.math.BigInteger.ZERO).add(_74___accumulator);
      } else {
        _74___accumulator = (_74___accumulator).add(java.math.BigInteger.ONE);
        dafny.DafnySequence<? extends __T> _in0 = (xs).drop(java.math.BigInteger.ONE);
        __T _in1 = v;
        xs = _in0;
        v = _in1;
        continue TAIL_CALL_START;
      }
    }
  }
  public static <__T> Std.Wrappers.Option<java.math.BigInteger> IndexOfOption(dafny.TypeDescriptor<__T> _td___T, dafny.DafnySequence<? extends __T> xs, __T v)
  {
    return __default.<__T>IndexByOption(_td___T, xs, ((java.util.function.Function<__T, java.util.function.Function<__T, Boolean>>)(_75_v) -> ((java.util.function.Function<__T, Boolean>)(_76_x_boxed0) -> {
      __T _76_x = ((__T)(java.lang.Object)(_76_x_boxed0));
      return java.util.Objects.equals(_76_x, _75_v);
    })).apply(v));
  }
  public static <__T> Std.Wrappers.Option<java.math.BigInteger> IndexByOption(dafny.TypeDescriptor<__T> _td___T, dafny.DafnySequence<? extends __T> xs, java.util.function.Function<__T, Boolean> p)
  {
    if ((java.math.BigInteger.valueOf((xs).length())).signum() == 0) {
      return Std.Wrappers.Option.<java.math.BigInteger>create_None(dafny.TypeDescriptor.BIG_INTEGER);
    } else if (((boolean)(java.lang.Object)((p).apply(((__T)(java.lang.Object)((xs).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))))))) {
      return Std.Wrappers.Option.<java.math.BigInteger>create_Some(dafny.TypeDescriptor.BIG_INTEGER, java.math.BigInteger.ZERO);
    } else {
      Std.Wrappers.Option<java.math.BigInteger> _77_o_k = __default.<__T>IndexByOption(_td___T, (xs).drop(java.math.BigInteger.ONE), p);
      if ((_77_o_k).is_Some()) {
        return Std.Wrappers.Option.<java.math.BigInteger>create_Some(dafny.TypeDescriptor.BIG_INTEGER, ((_77_o_k).dtor_value()).add(java.math.BigInteger.ONE));
      } else {
        return Std.Wrappers.Option.<java.math.BigInteger>create_None(dafny.TypeDescriptor.BIG_INTEGER);
      }
    }
  }
  public static <__T> java.math.BigInteger LastIndexOf(dafny.TypeDescriptor<__T> _td___T, dafny.DafnySequence<? extends __T> xs, __T v)
  {
    TAIL_CALL_START: while (true) {
      if (java.util.Objects.equals(((__T)(java.lang.Object)((xs).select(dafny.Helpers.toInt(((java.math.BigInteger.valueOf((xs).length())).subtract(java.math.BigInteger.ONE)))))), v)) {
        return (java.math.BigInteger.valueOf((xs).length())).subtract(java.math.BigInteger.ONE);
      } else {
        dafny.DafnySequence<? extends __T> _in2 = (xs).take((java.math.BigInteger.valueOf((xs).length())).subtract(java.math.BigInteger.ONE));
        __T _in3 = v;
        xs = _in2;
        v = _in3;
        continue TAIL_CALL_START;
      }
    }
  }
  public static <__T> Std.Wrappers.Option<java.math.BigInteger> LastIndexOfOption(dafny.TypeDescriptor<__T> _td___T, dafny.DafnySequence<? extends __T> xs, __T v)
  {
    return __default.<__T>LastIndexByOption(_td___T, xs, ((java.util.function.Function<__T, java.util.function.Function<__T, Boolean>>)(_78_v) -> ((java.util.function.Function<__T, Boolean>)(_79_x_boxed0) -> {
      __T _79_x = ((__T)(java.lang.Object)(_79_x_boxed0));
      return java.util.Objects.equals(_79_x, _78_v);
    })).apply(v));
  }
  public static <__T> Std.Wrappers.Option<java.math.BigInteger> LastIndexByOption(dafny.TypeDescriptor<__T> _td___T, dafny.DafnySequence<? extends __T> xs, java.util.function.Function<__T, Boolean> p)
  {
    TAIL_CALL_START: while (true) {
      if ((java.math.BigInteger.valueOf((xs).length())).signum() == 0) {
        return Std.Wrappers.Option.<java.math.BigInteger>create_None(dafny.TypeDescriptor.BIG_INTEGER);
      } else if (((boolean)(java.lang.Object)((p).apply(((__T)(java.lang.Object)((xs).select(dafny.Helpers.toInt(((java.math.BigInteger.valueOf((xs).length())).subtract(java.math.BigInteger.ONE)))))))))) {
        return Std.Wrappers.Option.<java.math.BigInteger>create_Some(dafny.TypeDescriptor.BIG_INTEGER, (java.math.BigInteger.valueOf((xs).length())).subtract(java.math.BigInteger.ONE));
      } else {
        dafny.DafnySequence<? extends __T> _in4 = (xs).take((java.math.BigInteger.valueOf((xs).length())).subtract(java.math.BigInteger.ONE));
        java.util.function.Function<__T, Boolean> _in5 = p;
        xs = _in4;
        p = _in5;
        continue TAIL_CALL_START;
      }
    }
  }
  public static <__T> dafny.DafnySequence<? extends __T> Remove(dafny.TypeDescriptor<__T> _td___T, dafny.DafnySequence<? extends __T> xs, java.math.BigInteger pos)
  {
    return dafny.DafnySequence.<__T>concatenate((xs).take(pos), (xs).drop((pos).add(java.math.BigInteger.ONE)));
  }
  public static <__T> dafny.DafnySequence<? extends __T> RemoveValue(dafny.TypeDescriptor<__T> _td___T, dafny.DafnySequence<? extends __T> xs, __T v)
  {
    if (!(xs).contains(v)) {
      return xs;
    } else {
      java.math.BigInteger _80_i = __default.<__T>IndexOf(_td___T, xs, v);
      return dafny.DafnySequence.<__T>concatenate((xs).take(_80_i), (xs).drop((_80_i).add(java.math.BigInteger.ONE)));
    }
  }
  public static <__T> dafny.DafnySequence<? extends __T> Insert(dafny.TypeDescriptor<__T> _td___T, dafny.DafnySequence<? extends __T> xs, __T a, java.math.BigInteger pos)
  {
    return dafny.DafnySequence.<__T>concatenate(dafny.DafnySequence.<__T>concatenate((xs).take(pos), dafny.DafnySequence.<__T> of(_td___T, a)), (xs).drop(pos));
  }
  public static <__T> dafny.DafnySequence<? extends __T> Reverse(dafny.TypeDescriptor<__T> _td___T, dafny.DafnySequence<? extends __T> xs)
  {
    dafny.DafnySequence<? extends __T> _81___accumulator = dafny.DafnySequence.<__T> empty(_td___T);
    TAIL_CALL_START: while (true) {
      if ((xs).equals(dafny.DafnySequence.<__T> empty(_td___T))) {
        return dafny.DafnySequence.<__T>concatenate(_81___accumulator, dafny.DafnySequence.<__T> empty(_td___T));
      } else {
        _81___accumulator = dafny.DafnySequence.<__T>concatenate(_81___accumulator, dafny.DafnySequence.<__T> of(_td___T, ((__T)(java.lang.Object)((xs).select(dafny.Helpers.toInt(((java.math.BigInteger.valueOf((xs).length())).subtract(java.math.BigInteger.ONE))))))));
        dafny.DafnySequence<? extends __T> _in6 = (xs).subsequence(dafny.Helpers.toInt((java.math.BigInteger.ZERO)), dafny.Helpers.toInt(((java.math.BigInteger.valueOf((xs).length())).subtract(java.math.BigInteger.ONE))));
        xs = _in6;
        continue TAIL_CALL_START;
      }
    }
  }
  public static <__T> dafny.DafnySequence<? extends __T> Repeat(dafny.TypeDescriptor<__T> _td___T, __T v, java.math.BigInteger length)
  {
    dafny.DafnySequence<? extends __T> _82___accumulator = dafny.DafnySequence.<__T> empty(_td___T);
    TAIL_CALL_START: while (true) {
      if ((length).signum() == 0) {
        return dafny.DafnySequence.<__T>concatenate(_82___accumulator, dafny.DafnySequence.<__T> empty(_td___T));
      } else {
        _82___accumulator = dafny.DafnySequence.<__T>concatenate(_82___accumulator, dafny.DafnySequence.<__T> of(_td___T, v));
        __T _in7 = v;
        java.math.BigInteger _in8 = (length).subtract(java.math.BigInteger.ONE);
        v = _in7;
        length = _in8;
        continue TAIL_CALL_START;
      }
    }
  }
  public static <__A, __B> dafny.Tuple2<dafny.DafnySequence<? extends __A>, dafny.DafnySequence<? extends __B>> Unzip(dafny.TypeDescriptor<__A> _td___A, dafny.TypeDescriptor<__B> _td___B, dafny.DafnySequence<? extends dafny.Tuple2<__A, __B>> xs)
  {
    if ((java.math.BigInteger.valueOf((xs).length())).signum() == 0) {
      return dafny.Tuple2.<dafny.DafnySequence<? extends __A>, dafny.DafnySequence<? extends __B>>create(dafny.DafnySequence.<__A> empty(_td___A), dafny.DafnySequence.<__B> empty(_td___B));
    } else {
      dafny.Tuple2<dafny.DafnySequence<? extends __A>, dafny.DafnySequence<? extends __B>> _let_tmp_rhs0 = __default.<__A, __B>Unzip(_td___A, _td___B, __default.<dafny.Tuple2<__A, __B>>DropLast(dafny.Tuple2.<__A, __B>_typeDescriptor(_td___A, _td___B), xs));
      dafny.DafnySequence<? extends __A> _83_a = ((dafny.DafnySequence<? extends __A>)(java.lang.Object)(((dafny.Tuple2<dafny.DafnySequence<? extends __A>, dafny.DafnySequence<? extends __B>>)_let_tmp_rhs0).dtor__0()));
      dafny.DafnySequence<? extends __B> _84_b = ((dafny.DafnySequence<? extends __B>)(java.lang.Object)(((dafny.Tuple2<dafny.DafnySequence<? extends __A>, dafny.DafnySequence<? extends __B>>)_let_tmp_rhs0).dtor__1()));
      return dafny.Tuple2.<dafny.DafnySequence<? extends __A>, dafny.DafnySequence<? extends __B>>create(dafny.DafnySequence.<__A>concatenate(_83_a, dafny.DafnySequence.<__A> of(_td___A, (__default.<dafny.Tuple2<__A, __B>>Last(dafny.Tuple2.<__A, __B>_typeDescriptor(_td___A, _td___B), xs)).dtor__0())), dafny.DafnySequence.<__B>concatenate(_84_b, dafny.DafnySequence.<__B> of(_td___B, (__default.<dafny.Tuple2<__A, __B>>Last(dafny.Tuple2.<__A, __B>_typeDescriptor(_td___A, _td___B), xs)).dtor__1())));
    }
  }
  public static <__A, __B> dafny.DafnySequence<? extends dafny.Tuple2<__A, __B>> Zip(dafny.TypeDescriptor<__A> _td___A, dafny.TypeDescriptor<__B> _td___B, dafny.DafnySequence<? extends __A> xs, dafny.DafnySequence<? extends __B> ys)
  {
    dafny.DafnySequence<? extends dafny.Tuple2<__A, __B>> _85___accumulator = dafny.DafnySequence.<dafny.Tuple2<__A, __B>> empty(dafny.Tuple2.<__A, __B>_typeDescriptor(_td___A, _td___B));
    TAIL_CALL_START: while (true) {
      if ((java.math.BigInteger.valueOf((xs).length())).signum() == 0) {
        return dafny.DafnySequence.<dafny.Tuple2<__A, __B>>concatenate(dafny.DafnySequence.<dafny.Tuple2<__A, __B>> empty(dafny.Tuple2.<__A, __B>_typeDescriptor(_td___A, _td___B)), _85___accumulator);
      } else {
        _85___accumulator = dafny.DafnySequence.<dafny.Tuple2<__A, __B>>concatenate(dafny.DafnySequence.<dafny.Tuple2<__A, __B>> of(dafny.Tuple2.<__A, __B>_typeDescriptor(_td___A, _td___B), dafny.Tuple2.<__A, __B>create(__default.<__A>Last(_td___A, xs), __default.<__B>Last(_td___B, ys))), _85___accumulator);
        dafny.DafnySequence<? extends __A> _in9 = __default.<__A>DropLast(_td___A, xs);
        dafny.DafnySequence<? extends __B> _in10 = __default.<__B>DropLast(_td___B, ys);
        xs = _in9;
        ys = _in10;
        continue TAIL_CALL_START;
      }
    }
  }
  public static java.math.BigInteger Max(dafny.DafnySequence<? extends java.math.BigInteger> xs) {
    if (java.util.Objects.equals(java.math.BigInteger.valueOf((xs).length()), java.math.BigInteger.ONE)) {
      return ((java.math.BigInteger)(java.lang.Object)((xs).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    } else {
      return Std.Math.__default.Max(((java.math.BigInteger)(java.lang.Object)((xs).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))), __default.Max((xs).drop(java.math.BigInteger.ONE)));
    }
  }
  public static java.math.BigInteger Min(dafny.DafnySequence<? extends java.math.BigInteger> xs) {
    if (java.util.Objects.equals(java.math.BigInteger.valueOf((xs).length()), java.math.BigInteger.ONE)) {
      return ((java.math.BigInteger)(java.lang.Object)((xs).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))));
    } else {
      return Std.Math.__default.Min(((java.math.BigInteger)(java.lang.Object)((xs).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))), __default.Min((xs).drop(java.math.BigInteger.ONE)));
    }
  }
  public static <__T> dafny.DafnySequence<? extends __T> Flatten(dafny.TypeDescriptor<__T> _td___T, dafny.DafnySequence<? extends dafny.DafnySequence<? extends __T>> xs)
  {
    dafny.DafnySequence<? extends __T> _86___accumulator = dafny.DafnySequence.<__T> empty(_td___T);
    TAIL_CALL_START: while (true) {
      if ((java.math.BigInteger.valueOf((xs).length())).signum() == 0) {
        return dafny.DafnySequence.<__T>concatenate(_86___accumulator, dafny.DafnySequence.<__T> empty(_td___T));
      } else {
        _86___accumulator = dafny.DafnySequence.<__T>concatenate(_86___accumulator, ((dafny.DafnySequence<? extends __T>)(java.lang.Object)((xs).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))));
        dafny.DafnySequence<? extends dafny.DafnySequence<? extends __T>> _in11 = (xs).drop(java.math.BigInteger.ONE);
        xs = _in11;
        continue TAIL_CALL_START;
      }
    }
  }
  public static <__T> dafny.DafnySequence<? extends __T> FlattenReverse(dafny.TypeDescriptor<__T> _td___T, dafny.DafnySequence<? extends dafny.DafnySequence<? extends __T>> xs)
  {
    dafny.DafnySequence<? extends __T> _87___accumulator = dafny.DafnySequence.<__T> empty(_td___T);
    TAIL_CALL_START: while (true) {
      if ((java.math.BigInteger.valueOf((xs).length())).signum() == 0) {
        return dafny.DafnySequence.<__T>concatenate(dafny.DafnySequence.<__T> empty(_td___T), _87___accumulator);
      } else {
        _87___accumulator = dafny.DafnySequence.<__T>concatenate(__default.<dafny.DafnySequence<? extends __T>>Last(dafny.DafnySequence.<__T>_typeDescriptor(_td___T), xs), _87___accumulator);
        dafny.DafnySequence<? extends dafny.DafnySequence<? extends __T>> _in12 = __default.<dafny.DafnySequence<? extends __T>>DropLast(dafny.DafnySequence.<__T>_typeDescriptor(_td___T), xs);
        xs = _in12;
        continue TAIL_CALL_START;
      }
    }
  }
  public static <__T> dafny.DafnySequence<? extends __T> Join(dafny.TypeDescriptor<__T> _td___T, dafny.DafnySequence<? extends dafny.DafnySequence<? extends __T>> seqs, dafny.DafnySequence<? extends __T> separator)
  {
    dafny.DafnySequence<? extends __T> _88___accumulator = dafny.DafnySequence.<__T> empty(_td___T);
    TAIL_CALL_START: while (true) {
      if ((java.math.BigInteger.valueOf((seqs).length())).signum() == 0) {
        return dafny.DafnySequence.<__T>concatenate(_88___accumulator, dafny.DafnySequence.<__T> empty(_td___T));
      } else if (java.util.Objects.equals(java.math.BigInteger.valueOf((seqs).length()), java.math.BigInteger.ONE)) {
        return dafny.DafnySequence.<__T>concatenate(_88___accumulator, ((dafny.DafnySequence<? extends __T>)(java.lang.Object)((seqs).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))));
      } else {
        _88___accumulator = dafny.DafnySequence.<__T>concatenate(_88___accumulator, dafny.DafnySequence.<__T>concatenate(((dafny.DafnySequence<? extends __T>)(java.lang.Object)((seqs).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))), separator));
        dafny.DafnySequence<? extends dafny.DafnySequence<? extends __T>> _in13 = (seqs).drop(java.math.BigInteger.ONE);
        dafny.DafnySequence<? extends __T> _in14 = separator;
        seqs = _in13;
        separator = _in14;
        continue TAIL_CALL_START;
      }
    }
  }
  public static <__T> dafny.DafnySequence<? extends dafny.DafnySequence<? extends __T>> Split(dafny.TypeDescriptor<__T> _td___T, dafny.DafnySequence<? extends __T> s, __T delim)
  {
    dafny.DafnySequence<? extends dafny.DafnySequence<? extends __T>> _89___accumulator = dafny.DafnySequence.<dafny.DafnySequence<? extends __T>> empty(dafny.DafnySequence.<__T>_typeDescriptor(_td___T));
    TAIL_CALL_START: while (true) {
      Std.Wrappers.Option<java.math.BigInteger> _90_i = __default.<__T>IndexOfOption(_td___T, s, delim);
      if ((_90_i).is_Some()) {
        _89___accumulator = dafny.DafnySequence.<dafny.DafnySequence<? extends __T>>concatenate(_89___accumulator, dafny.DafnySequence.<dafny.DafnySequence<? extends __T>> of(dafny.DafnySequence.<__T>_typeDescriptor(_td___T), (s).take((_90_i).dtor_value())));
        dafny.DafnySequence<? extends __T> _in15 = (s).drop(((_90_i).dtor_value()).add(java.math.BigInteger.ONE));
        __T _in16 = delim;
        s = _in15;
        delim = _in16;
        continue TAIL_CALL_START;
      } else {
        return dafny.DafnySequence.<dafny.DafnySequence<? extends __T>>concatenate(_89___accumulator, dafny.DafnySequence.<dafny.DafnySequence<? extends __T>> of(dafny.DafnySequence.<__T>_typeDescriptor(_td___T), s));
      }
    }
  }
  public static <__T> dafny.Tuple2<dafny.DafnySequence<? extends __T>, dafny.DafnySequence<? extends __T>> SplitOnce(dafny.TypeDescriptor<__T> _td___T, dafny.DafnySequence<? extends __T> s, __T delim)
  {
    Std.Wrappers.Option<java.math.BigInteger> _91_i = __default.<__T>IndexOfOption(_td___T, s, delim);
    return dafny.Tuple2.<dafny.DafnySequence<? extends __T>, dafny.DafnySequence<? extends __T>>create((s).take((_91_i).dtor_value()), (s).drop(((_91_i).dtor_value()).add(java.math.BigInteger.ONE)));
  }
  public static <__T> Std.Wrappers.Option<dafny.Tuple2<dafny.DafnySequence<? extends __T>, dafny.DafnySequence<? extends __T>>> SplitOnceOption(dafny.TypeDescriptor<__T> _td___T, dafny.DafnySequence<? extends __T> s, __T delim)
  {
    Std.Wrappers.Option<java.math.BigInteger> _92_valueOrError0 = __default.<__T>IndexOfOption(_td___T, s, delim);
    if ((_92_valueOrError0).IsFailure(_System.nat._typeDescriptor())) {
      return (_92_valueOrError0).<dafny.Tuple2<dafny.DafnySequence<? extends __T>, dafny.DafnySequence<? extends __T>>>PropagateFailure(_System.nat._typeDescriptor(), dafny.Tuple2.<dafny.DafnySequence<? extends __T>, dafny.DafnySequence<? extends __T>>_typeDescriptor(dafny.DafnySequence.<__T>_typeDescriptor(_td___T), dafny.DafnySequence.<__T>_typeDescriptor(_td___T)));
    } else {
      java.math.BigInteger _93_i = (_92_valueOrError0).Extract(_System.nat._typeDescriptor());
      return Std.Wrappers.Option.<dafny.Tuple2<dafny.DafnySequence<? extends __T>, dafny.DafnySequence<? extends __T>>>create_Some(dafny.Tuple2.<dafny.DafnySequence<? extends __T>, dafny.DafnySequence<? extends __T>>_typeDescriptor(dafny.DafnySequence.<__T>_typeDescriptor(_td___T), dafny.DafnySequence.<__T>_typeDescriptor(_td___T)), dafny.Tuple2.<dafny.DafnySequence<? extends __T>, dafny.DafnySequence<? extends __T>>create((s).take(_93_i), (s).drop((_93_i).add(java.math.BigInteger.ONE))));
    }
  }
  public static <__T, __R> dafny.DafnySequence<? extends __R> Map(dafny.TypeDescriptor<__T> _td___T, dafny.TypeDescriptor<__R> _td___R, java.util.function.Function<__T, __R> f, dafny.DafnySequence<? extends __T> xs)
  {
    dafny.DafnySequence<? extends __R> _94___accumulator = dafny.DafnySequence.<__R> empty(_td___R);
    TAIL_CALL_START: while (true) {
      if ((java.math.BigInteger.valueOf((xs).length())).signum() == 0) {
        return dafny.DafnySequence.<__R>concatenate(_94___accumulator, dafny.DafnySequence.<__R> empty(_td___R));
      } else {
        _94___accumulator = dafny.DafnySequence.<__R>concatenate(_94___accumulator, dafny.DafnySequence.<__R> of(_td___R, ((__R)(java.lang.Object)((f).apply(((__T)(java.lang.Object)((xs).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))))))));
        java.util.function.Function<__T, __R> _in17 = f;
        dafny.DafnySequence<? extends __T> _in18 = (xs).drop(java.math.BigInteger.ONE);
        f = _in17;
        xs = _in18;
        continue TAIL_CALL_START;
      }
    }
  }
  public static <__T, __R, __E> Std.Wrappers.Result<dafny.DafnySequence<? extends __R>, __E> MapWithResult(dafny.TypeDescriptor<__T> _td___T, dafny.TypeDescriptor<__R> _td___R, dafny.TypeDescriptor<__E> _td___E, java.util.function.Function<__T, Std.Wrappers.Result<__R, __E>> f, dafny.DafnySequence<? extends __T> xs)
  {
    if ((java.math.BigInteger.valueOf((xs).length())).signum() == 0) {
      return Std.Wrappers.Result.<dafny.DafnySequence<? extends __R>, __E>create_Success(dafny.DafnySequence.<__R>_typeDescriptor(_td___R), _td___E, dafny.DafnySequence.<__R> empty(_td___R));
    } else {
      Std.Wrappers.Result<__R, __E> _95_valueOrError0 = ((Std.Wrappers.Result<__R, __E>)(java.lang.Object)((f).apply(((__T)(java.lang.Object)((xs).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))))));
      if ((_95_valueOrError0).IsFailure(_td___R, _td___E)) {
        return (_95_valueOrError0).<dafny.DafnySequence<? extends __R>>PropagateFailure(_td___R, _td___E, dafny.DafnySequence.<__R>_typeDescriptor(_td___R));
      } else {
        __R _96_head = (_95_valueOrError0).Extract(_td___R, _td___E);
        Std.Wrappers.Result<dafny.DafnySequence<? extends __R>, __E> _97_valueOrError1 = __default.<__T, __R, __E>MapWithResult(_td___T, _td___R, _td___E, f, (xs).drop(java.math.BigInteger.ONE));
        if ((_97_valueOrError1).IsFailure(dafny.DafnySequence.<__R>_typeDescriptor(_td___R), _td___E)) {
          return (_97_valueOrError1).<dafny.DafnySequence<? extends __R>>PropagateFailure(dafny.DafnySequence.<__R>_typeDescriptor(_td___R), _td___E, dafny.DafnySequence.<__R>_typeDescriptor(_td___R));
        } else {
          dafny.DafnySequence<? extends __R> _98_tail = (_97_valueOrError1).Extract(dafny.DafnySequence.<__R>_typeDescriptor(_td___R), _td___E);
          return Std.Wrappers.Result.<dafny.DafnySequence<? extends __R>, __E>create_Success(dafny.DafnySequence.<__R>_typeDescriptor(_td___R), _td___E, dafny.DafnySequence.<__R>concatenate(dafny.DafnySequence.<__R> of(_td___R, _96_head), _98_tail));
        }
      }
    }
  }
  public static <__T> dafny.DafnySequence<? extends __T> Filter(dafny.TypeDescriptor<__T> _td___T, java.util.function.Function<__T, Boolean> f, dafny.DafnySequence<? extends __T> xs)
  {
    dafny.DafnySequence<? extends __T> _99___accumulator = dafny.DafnySequence.<__T> empty(_td___T);
    TAIL_CALL_START: while (true) {
      if ((java.math.BigInteger.valueOf((xs).length())).signum() == 0) {
        return dafny.DafnySequence.<__T>concatenate(_99___accumulator, dafny.DafnySequence.<__T> empty(_td___T));
      } else {
        _99___accumulator = dafny.DafnySequence.<__T>concatenate(_99___accumulator, ((((boolean)(java.lang.Object)((f).apply(((__T)(java.lang.Object)((xs).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))))))) ? (dafny.DafnySequence.<__T> of(_td___T, ((__T)(java.lang.Object)((xs).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))))) : (dafny.DafnySequence.<__T> empty(_td___T))));
        java.util.function.Function<__T, Boolean> _in19 = f;
        dafny.DafnySequence<? extends __T> _in20 = (xs).drop(java.math.BigInteger.ONE);
        f = _in19;
        xs = _in20;
        continue TAIL_CALL_START;
      }
    }
  }
  public static <__A, __T> __A FoldLeft(dafny.TypeDescriptor<__A> _td___A, dafny.TypeDescriptor<__T> _td___T, dafny.Function2<__A, __T, __A> f, __A init, dafny.DafnySequence<? extends __T> xs)
  {
    TAIL_CALL_START: while (true) {
      if ((java.math.BigInteger.valueOf((xs).length())).signum() == 0) {
        return init;
      } else {
        dafny.Function2<__A, __T, __A> _in21 = f;
        __A _in22 = ((__A)(java.lang.Object)((f).apply(init, ((__T)(java.lang.Object)((xs).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))))));
        dafny.DafnySequence<? extends __T> _in23 = (xs).drop(java.math.BigInteger.ONE);
        f = _in21;
        init = _in22;
        xs = _in23;
        continue TAIL_CALL_START;
      }
    }
  }
  public static <__A, __T> __A FoldRight(dafny.TypeDescriptor<__A> _td___A, dafny.TypeDescriptor<__T> _td___T, dafny.Function2<__T, __A, __A> f, dafny.DafnySequence<? extends __T> xs, __A init)
  {
    if ((java.math.BigInteger.valueOf((xs).length())).signum() == 0) {
      return init;
    } else {
      return ((__A)(java.lang.Object)((f).apply(((__T)(java.lang.Object)((xs).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))), __default.<__A, __T>FoldRight(_td___A, _td___T, f, (xs).drop(java.math.BigInteger.ONE), init))));
    }
  }
  public static <__T> dafny.DafnySequence<? extends __T> SetToSeq(dafny.TypeDescriptor<__T> _td___T, dafny.DafnySet<? extends __T> s)
  {
    dafny.DafnySequence<? extends __T> xs = dafny.DafnySequence.<__T> empty(_td___T);
    if(true) {
      xs = dafny.DafnySequence.<__T> empty(_td___T);
      dafny.DafnySet<? extends __T> _100_left;
      _100_left = s;
      while (!(_100_left).equals(dafny.DafnySet.<__T> empty())) {
        @SuppressWarnings({"unchecked", "deprecation"})
        __T _101_x;
        goto__ASSIGN_SUCH_THAT_0: {
          for (__T _assign_such_that_0_boxed0 : (_100_left).Elements()) {
            __T _assign_such_that_0 = ((__T)(java.lang.Object)(_assign_such_that_0_boxed0));
            if (true) {
              _101_x = (__T)_assign_such_that_0;
              if ((_100_left).<__T>contains(_101_x)) {
                break goto__ASSIGN_SUCH_THAT_0;
              }
            }
          }
          throw new IllegalArgumentException("assign-such-that search produced no value (line 7231)");
        }
        _100_left = dafny.DafnySet.<__T>difference(_100_left, dafny.DafnySet.<__T> of(_101_x));
        xs = dafny.DafnySequence.<__T>concatenate(xs, dafny.DafnySequence.<__T> of(_td___T, _101_x));
      }
    }
    return xs;
  }
  public static <__T> dafny.DafnySequence<? extends __T> SetToSortedSeq(dafny.TypeDescriptor<__T> _td___T, dafny.DafnySet<? extends __T> s, dafny.Function2<__T, __T, Boolean> R)
  {
    dafny.DafnySequence<? extends __T> xs = dafny.DafnySequence.<__T> empty(_td___T);
    if(true) {
      dafny.DafnySequence<? extends __T> _out0;
      _out0 = __default.<__T>SetToSeq(_td___T, s);
      xs = _out0;
      xs = __default.<__T>MergeSortBy(_td___T, R, xs);
    }
    return xs;
  }
  public static <__T> dafny.DafnySequence<? extends __T> MergeSortBy(dafny.TypeDescriptor<__T> _td___T, dafny.Function2<__T, __T, Boolean> lessThanOrEq, dafny.DafnySequence<? extends __T> a)
  {
    if ((java.math.BigInteger.valueOf((a).length())).compareTo(java.math.BigInteger.ONE) <= 0) {
      return a;
    } else {
      java.math.BigInteger _102_splitIndex = dafny.DafnyEuclidean.EuclideanDivision(java.math.BigInteger.valueOf((a).length()), java.math.BigInteger.valueOf(2L));
      dafny.DafnySequence<? extends __T> _103_left = (a).take(_102_splitIndex);
      dafny.DafnySequence<? extends __T> _104_right = (a).drop(_102_splitIndex);
      dafny.DafnySequence<? extends __T> _105_leftSorted = __default.<__T>MergeSortBy(_td___T, lessThanOrEq, _103_left);
      dafny.DafnySequence<? extends __T> _106_rightSorted = __default.<__T>MergeSortBy(_td___T, lessThanOrEq, _104_right);
      return __default.<__T>MergeSortedWith(_td___T, _105_leftSorted, _106_rightSorted, lessThanOrEq);
    }
  }
  public static <__T> dafny.DafnySequence<? extends __T> MergeSortedWith(dafny.TypeDescriptor<__T> _td___T, dafny.DafnySequence<? extends __T> left, dafny.DafnySequence<? extends __T> right, dafny.Function2<__T, __T, Boolean> lessThanOrEq)
  {
    dafny.DafnySequence<? extends __T> _107___accumulator = dafny.DafnySequence.<__T> empty(_td___T);
    TAIL_CALL_START: while (true) {
      if ((java.math.BigInteger.valueOf((left).length())).signum() == 0) {
        return dafny.DafnySequence.<__T>concatenate(_107___accumulator, right);
      } else if ((java.math.BigInteger.valueOf((right).length())).signum() == 0) {
        return dafny.DafnySequence.<__T>concatenate(_107___accumulator, left);
      } else if (((boolean)(java.lang.Object)((lessThanOrEq).apply(((__T)(java.lang.Object)((left).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))), ((__T)(java.lang.Object)((right).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))))))) {
        _107___accumulator = dafny.DafnySequence.<__T>concatenate(_107___accumulator, dafny.DafnySequence.<__T> of(_td___T, ((__T)(java.lang.Object)((left).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))))));
        dafny.DafnySequence<? extends __T> _in24 = (left).drop(java.math.BigInteger.ONE);
        dafny.DafnySequence<? extends __T> _in25 = right;
        dafny.Function2<__T, __T, Boolean> _in26 = lessThanOrEq;
        left = _in24;
        right = _in25;
        lessThanOrEq = _in26;
        continue TAIL_CALL_START;
      } else {
        _107___accumulator = dafny.DafnySequence.<__T>concatenate(_107___accumulator, dafny.DafnySequence.<__T> of(_td___T, ((__T)(java.lang.Object)((right).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO)))))));
        dafny.DafnySequence<? extends __T> _in27 = left;
        dafny.DafnySequence<? extends __T> _in28 = (right).drop(java.math.BigInteger.ONE);
        dafny.Function2<__T, __T, Boolean> _in29 = lessThanOrEq;
        left = _in27;
        right = _in28;
        lessThanOrEq = _in29;
        continue TAIL_CALL_START;
      }
    }
  }
  @Override
  public java.lang.String toString() {
    return "Std.Collections.Seq._default";
  }
}
