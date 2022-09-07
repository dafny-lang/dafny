// Class ArraySequence
// Dafny class ArraySequence compiled into Java
package Dafny;


@SuppressWarnings({"unchecked", "deprecation"})
public class ArraySequence<T> implements Sequence<T> {
  private dafny.TypeDescriptor<T> _td_T;
  public ArraySequence(dafny.TypeDescriptor<T> _td_T) {
    this._td_T = _td_T;
    this._value = null;
  }
  public int HashCode()
  {
    int _out11;
    _out11 = Dafny._Companion_Sequence.<T>HashCode(_td_T, this);
    return _out11;
  }
  public dafny.DafnySequence<? extends Character> ToString()
  {
    dafny.DafnySequence<? extends Character> _out12;
    _out12 = Dafny._Companion_Sequence.<T>ToString(_td_T, this);
    return _out12;
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
  public void __ctor(ImmutableArray<T> value)
  {
    (this)._value = value;
  }
  public java.math.BigInteger Length() {
    return ((this).value()).Length();
  }
  public ImmutableArray<T> ToArray()
  {
    ImmutableArray<T> ret = null;
    ret = (this).value();
    return ret;
  }
  public ImmutableArray<T> _value;
  public ImmutableArray<T> value()
  {
    return this._value;
  }
  public static <T> dafny.TypeDescriptor<ArraySequence<T>> _typeDescriptor(dafny.TypeDescriptor<T> _td_T) {
    return (dafny.TypeDescriptor<ArraySequence<T>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.referenceWithInitializer(ArraySequence.class, () -> (ArraySequence<T>) null);
  }
}
