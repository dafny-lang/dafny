// Class ConcatSequence
// Dafny class ConcatSequence compiled into Java
package Dafny;


@SuppressWarnings({"unchecked", "deprecation"})
public class ConcatSequence<T> implements Sequence<T> {
  private dafny.TypeDescriptor<T> _td_T;
  public ConcatSequence(dafny.TypeDescriptor<T> _td_T) {
    this._td_T = _td_T;
    this._left = null;
    this._right = null;
    this._length = java.math.BigInteger.ZERO;
  }
  public T Select(java.math.BigInteger index)
  {
    @SuppressWarnings({"unchecked", "deprecation"})
    T _out13;
    _out13 = Dafny._Companion_Sequence.<T>Select(_td_T, this, index);
    return _out13;
  }
  public Sequence<T> Drop(java.math.BigInteger lo)
  {
    Sequence<T> _out14;
    _out14 = Dafny._Companion_Sequence.<T>Drop(_td_T, this, lo);
    return _out14;
  }
  public Sequence<T> Take(java.math.BigInteger hi)
  {
    Sequence<T> _out15;
    _out15 = Dafny._Companion_Sequence.<T>Take(_td_T, this, hi);
    return _out15;
  }
  public Sequence<T> Subsequence(java.math.BigInteger lo, java.math.BigInteger hi)
  {
    Sequence<T> _out16;
    _out16 = Dafny._Companion_Sequence.<T>Subsequence(_td_T, this, lo, hi);
    return _out16;
  }
  public void __ctor(Sequence<T> left, Sequence<T> right)
  {
    (this)._left = left;
    (this)._right = right;
    (this)._length = ((left).Length()).add(((right).Length()));
  }
  public java.math.BigInteger Length() {
    return (this).length();
  }
  public ImmutableArray<T> ToArray()
  {
    ImmutableArray<T> ret = null;
    if(true) {
      Vector<T> _7_builder;
      Vector<T> _nw1 = new Vector<T>(_td_T);
      _nw1.__ctor((this).length());
      _7_builder = _nw1;
      Vector<Sequence<T>> _8_stack;
      Vector<Sequence<T>> _nw2 = new Vector<Sequence<T>>(Dafny._Companion_Sequence.<T>_typeDescriptor(_td_T));
      _nw2.__ctor(java.math.BigInteger.valueOf(10L));
      _8_stack = _nw2;
      __default.<T>AppendOptimized(_td_T, _7_builder, this, _8_stack);
      ImmutableArray<T> _out17;
      _out17 = (_7_builder).Freeze();
      ret = _out17;
    }
    return ret;
  }
  public Sequence<T> _left;
  public Sequence<T> left()
  {
    return this._left;
  }
  public Sequence<T> _right;
  public Sequence<T> right()
  {
    return this._right;
  }
  public java.math.BigInteger _length;
  public java.math.BigInteger length()
  {
    return this._length;
  }
  public static <T> dafny.TypeDescriptor<ConcatSequence<T>> _typeDescriptor(dafny.TypeDescriptor<T> _td_T) {
    return (dafny.TypeDescriptor<ConcatSequence<T>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.referenceWithInitializer(ConcatSequence.class, () -> (ConcatSequence<T>) null);
  }
}
