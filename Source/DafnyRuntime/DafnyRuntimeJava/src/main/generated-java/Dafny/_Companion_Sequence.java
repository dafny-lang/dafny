// Interface Sequence
// Dafny trait Sequence compiled into Java
package Dafny;


@SuppressWarnings({"unchecked", "deprecation"})
public class _Companion_Sequence<T> {
  public _Companion_Sequence() {
  }
  public static <T> dafny.TypeDescriptor<Sequence<T>> _typeDescriptor(dafny.TypeDescriptor<T> _td_T) {
    return (dafny.TypeDescriptor<Sequence<T>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.referenceWithInitializer(Sequence.class, () -> null);
  }
  public static <T> int HashCode(dafny.TypeDescriptor<T> _td_T, Sequence<T> _this)
  {
    int ret = 0;
    if(true) {
      ret = 0;
      java.math.BigInteger _hi0 = (_this).Length();
      for (java.math.BigInteger _4_i = java.math.BigInteger.ZERO; _4_i.compareTo(_hi0) < 0; _4_i = _4_i.add(java.math.BigInteger.ONE)) {
        @SuppressWarnings({"unchecked", "deprecation"})
        T _5_element;
        @SuppressWarnings({"unchecked", "deprecation"})
        T _out4;
        _out4 = (_this).Select(_4_i);
        _5_element = _out4;
        ret = (int)  (((int)  (((int) (((int)  ((ret) << (java.math.BigInteger.valueOf(3L)).intValue())))) | ((int)  ((ret) >>> (java.math.BigInteger.valueOf(29L)).intValue())))) ^ (Helpers_Compile.__default.<T>HashCode(_td_T, _5_element)));
      }
    }
    return ret;
  }
  public static <T> dafny.DafnySequence<? extends Character> ToString(dafny.TypeDescriptor<T> _td_T, Sequence<T> _this)
  {
    dafny.DafnySequence<? extends Character> ret = dafny.DafnySequence.<Character> empty(dafny.TypeDescriptor.CHAR);
    if(true) {
      ret = dafny.DafnySequence.asString("[");
      java.math.BigInteger _hi1 = (_this).Length();
      for (java.math.BigInteger _6_i = java.math.BigInteger.ZERO; _6_i.compareTo(_hi1) < 0; _6_i = _6_i.add(java.math.BigInteger.ONE)) {
        if ((_6_i).signum() != 0) {
          ret = dafny.DafnySequence.<Character>concatenate(ret, dafny.DafnySequence.asString(","));
        }
        @SuppressWarnings({"unchecked", "deprecation"})
        T _7_element;
        @SuppressWarnings({"unchecked", "deprecation"})
        T _out5;
        _out5 = (_this).Select(_6_i);
        _7_element = _out5;
        ret = dafny.DafnySequence.<Character>concatenate(ret, Helpers_Compile.__default.<T>ToString(_td_T, _7_element));
      }
      ret = dafny.DafnySequence.<Character>concatenate(ret, dafny.DafnySequence.asString("]"));
    }
    return ret;
  }
  public static <T> T Select(dafny.TypeDescriptor<T> _td_T, Sequence<T> _this, java.math.BigInteger index)
  {
    @SuppressWarnings({"unchecked", "deprecation"})
    T ret = null;
    ImmutableArray<T> _8_a;
    ImmutableArray<T> _out6;
    _out6 = (_this).ToArray();
    _8_a = _out6;
    ret = (_8_a).Select(index);
    return ret;
  }
  public static <T> Sequence<T> Drop(dafny.TypeDescriptor<T> _td_T, Sequence<T> _this, java.math.BigInteger lo)
  {
    Sequence<T> ret = null;
    if(true) {
      Sequence<T> _out7;
      _out7 = (_this).Subsequence(lo, (_this).Length());
      ret = _out7;
    }
    return ret;
  }
  public static <T> Sequence<T> Take(dafny.TypeDescriptor<T> _td_T, Sequence<T> _this, java.math.BigInteger hi)
  {
    Sequence<T> ret = null;
    if(true) {
      Sequence<T> _out8;
      _out8 = (_this).Subsequence(java.math.BigInteger.ZERO, hi);
      ret = _out8;
    }
    return ret;
  }
  public static <T> Sequence<T> Subsequence(dafny.TypeDescriptor<T> _td_T, Sequence<T> _this, java.math.BigInteger lo, java.math.BigInteger hi)
  {
    Sequence<T> ret = null;
    if(true) {
      ImmutableArray<T> _9_a;
      ImmutableArray<T> _out9;
      _out9 = (_this).ToArray();
      _9_a = _out9;
      ImmutableArray<T> _10_subarray;
      ImmutableArray<T> _out10;
      _out10 = (_9_a).Subarray(lo, hi);
      _10_subarray = _out10;
      ArraySequence<T> _nw0 = new ArraySequence<T>(_td_T);
      _nw0.__ctor(_10_subarray);
      ret = _nw0;
    }
    return ret;
  }
}
