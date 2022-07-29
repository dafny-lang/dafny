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
  public T Select(java.math.BigInteger index)
  {
    @SuppressWarnings({"unchecked", "deprecation"})
    T _out9;
    _out9 = Dafny._Companion_Sequence.<T>Select(_td_T, this, index);
    return _out9;
  }
  public Sequence<T> Drop(java.math.BigInteger lo)
  {
    Sequence<T> _out10;
    _out10 = Dafny._Companion_Sequence.<T>Drop(_td_T, this, lo);
    return _out10;
  }
  public Sequence<T> Take(java.math.BigInteger hi)
  {
    Sequence<T> _out11;
    _out11 = Dafny._Companion_Sequence.<T>Take(_td_T, this, hi);
    return _out11;
  }
  public Sequence<T> Subsequence(java.math.BigInteger lo, java.math.BigInteger hi)
  {
    Sequence<T> _out12;
    _out12 = Dafny._Companion_Sequence.<T>Subsequence(_td_T, this, lo, hi);
    return _out12;
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
