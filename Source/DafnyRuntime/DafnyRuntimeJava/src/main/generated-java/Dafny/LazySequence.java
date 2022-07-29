// Class LazySequence
// Dafny class LazySequence compiled into Java
package Dafny;


@SuppressWarnings({"unchecked", "deprecation"})
public class LazySequence<T> implements Sequence<T> {
  private dafny.TypeDescriptor<T> _td_T;
  public LazySequence(dafny.TypeDescriptor<T> _td_T) {
    this._td_T = _td_T;
    this._length = java.math.BigInteger.ZERO;
    this._box = null;
  }
  public T Select(java.math.BigInteger index)
  {
    @SuppressWarnings({"unchecked", "deprecation"})
    T _out18;
    _out18 = Dafny._Companion_Sequence.<T>Select(_td_T, this, index);
    return _out18;
  }
  public Sequence<T> Drop(java.math.BigInteger lo)
  {
    Sequence<T> _out19;
    _out19 = Dafny._Companion_Sequence.<T>Drop(_td_T, this, lo);
    return _out19;
  }
  public Sequence<T> Take(java.math.BigInteger hi)
  {
    Sequence<T> _out20;
    _out20 = Dafny._Companion_Sequence.<T>Take(_td_T, this, hi);
    return _out20;
  }
  public Sequence<T> Subsequence(java.math.BigInteger lo, java.math.BigInteger hi)
  {
    Sequence<T> _out21;
    _out21 = Dafny._Companion_Sequence.<T>Subsequence(_td_T, this, lo, hi);
    return _out21;
  }
  public void __ctor(Sequence<T> wrapped)
  {
    AtomicBox<Sequence<T>> _9_box;
    AtomicBox<Sequence<T>> _out22;
    _out22 = AtomicBox.<Sequence<T>>Make(Dafny._Companion_Sequence.<T>_typeDescriptor(_td_T), wrapped);
    _9_box = _out22;
    (this)._box = _9_box;
    (this)._length = (wrapped).Length();
  }
  public java.math.BigInteger Length() {
    return (this).length();
  }
  public ImmutableArray<T> ToArray()
  {
    ImmutableArray<T> ret = null;
    if(true) {
      Sequence<T> _10_expr;
      Sequence<T> _out23;
      _out23 = ((this).box()).Get();
      _10_expr = _out23;
      ImmutableArray<T> _out24;
      _out24 = (_10_expr).ToArray();
      ret = _out24;
      ArraySequence<T> _11_arraySeq;
      ArraySequence<T> _nw3 = new ArraySequence<T>(_td_T);
      _nw3.__ctor(ret);
      _11_arraySeq = _nw3;
      ((this).box()).Put(_11_arraySeq);
    }
    return ret;
  }
  public java.math.BigInteger _length;
  public java.math.BigInteger length()
  {
    return this._length;
  }
  public AtomicBox<Sequence<T>> _box;
  public AtomicBox<Sequence<T>> box()
  {
    return this._box;
  }
  public static <T> dafny.TypeDescriptor<LazySequence<T>> _typeDescriptor(dafny.TypeDescriptor<T> _td_T) {
    return (dafny.TypeDescriptor<LazySequence<T>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.referenceWithInitializer(LazySequence.class, () -> (LazySequence<T>) null);
  }
}
