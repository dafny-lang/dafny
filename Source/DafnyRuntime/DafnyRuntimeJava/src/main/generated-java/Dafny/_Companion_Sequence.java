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
  public static <T> T Select(dafny.TypeDescriptor<T> _td_T, Sequence<T> _this, java.math.BigInteger index)
  {
    @SuppressWarnings({"unchecked", "deprecation"})
    T ret = null;
    ImmutableArray<T> _4_a;
    ImmutableArray<T> _out4;
    _out4 = (_this).ToArray();
    _4_a = _out4;
    ret = (_4_a).At(index);
    return ret;
  }
  public static <T> Sequence<T> Drop(dafny.TypeDescriptor<T> _td_T, Sequence<T> _this, java.math.BigInteger lo)
  {
    Sequence<T> ret = null;
    if(true) {
      Sequence<T> _out5;
      _out5 = (_this).Subsequence(lo, (_this).Length());
      ret = _out5;
    }
    return ret;
  }
  public static <T> Sequence<T> Take(dafny.TypeDescriptor<T> _td_T, Sequence<T> _this, java.math.BigInteger hi)
  {
    Sequence<T> ret = null;
    if(true) {
      Sequence<T> _out6;
      _out6 = (_this).Subsequence(java.math.BigInteger.ZERO, hi);
      ret = _out6;
    }
    return ret;
  }
  public static <T> Sequence<T> Subsequence(dafny.TypeDescriptor<T> _td_T, Sequence<T> _this, java.math.BigInteger lo, java.math.BigInteger hi)
  {
    Sequence<T> ret = null;
    if(true) {
      ImmutableArray<T> _5_a;
      ImmutableArray<T> _out7;
      _out7 = (_this).ToArray();
      _5_a = _out7;
      ImmutableArray<T> _6_subarray;
      ImmutableArray<T> _out8;
      _out8 = (_5_a).Subarray(lo, hi);
      _6_subarray = _out8;
      ArraySequence<T> _nw0 = new ArraySequence<T>(_td_T);
      _nw0.__ctor(_6_subarray);
      ret = _nw0;
    }
    return ret;
  }
}
