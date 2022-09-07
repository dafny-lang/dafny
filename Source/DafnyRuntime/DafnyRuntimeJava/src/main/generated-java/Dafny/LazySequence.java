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
  public int HashCode()
  {
    int _out24;
    _out24 = Dafny._Companion_Sequence.<T>HashCode(_td_T, this);
    return _out24;
  }
  public dafny.DafnySequence<? extends Character> ToString()
  {
    dafny.DafnySequence<? extends Character> _out25;
    _out25 = Dafny._Companion_Sequence.<T>ToString(_td_T, this);
    return _out25;
  }
  public T Select(java.math.BigInteger index)
  {
    @SuppressWarnings({"unchecked", "deprecation"})
    T _out26;
    _out26 = Dafny._Companion_Sequence.<T>Select(_td_T, this, index);
    return _out26;
  }
  public Sequence<T> Drop(java.math.BigInteger lo)
  {
    Sequence<T> _out27;
    _out27 = Dafny._Companion_Sequence.<T>Drop(_td_T, this, lo);
    return _out27;
  }
  public Sequence<T> Take(java.math.BigInteger hi)
  {
    Sequence<T> _out28;
    _out28 = Dafny._Companion_Sequence.<T>Take(_td_T, this, hi);
    return _out28;
  }
  public Sequence<T> Subsequence(java.math.BigInteger lo, java.math.BigInteger hi)
  {
    Sequence<T> _out29;
    _out29 = Dafny._Companion_Sequence.<T>Subsequence(_td_T, this, lo, hi);
    return _out29;
  }
  public void __ctor(Sequence<T> wrapped)
  {
    AtomicBox<Sequence<T>> _13_box;
    AtomicBox<Sequence<T>> _out30;
    _out30 = AtomicBox.<Sequence<T>>Make(Dafny._Companion_Sequence.<T>_typeDescriptor(_td_T), wrapped);
    _13_box = _out30;
    (this)._box = _13_box;
    (this)._length = (wrapped).Length();
  }
  public java.math.BigInteger Length() {
    return (this).length();
  }
  public ImmutableArray<T> ToArray()
  {
    ImmutableArray<T> ret = null;
    if(true) {
      Sequence<T> _14_expr;
      Sequence<T> _out31;
      _out31 = ((this).box()).Get();
      _14_expr = _out31;
      ImmutableArray<T> _out32;
      _out32 = (_14_expr).ToArray();
      ret = _out32;
      ArraySequence<T> _15_arraySeq;
      ArraySequence<T> _nw3 = new ArraySequence<T>(_td_T);
      _nw3.__ctor(ret);
      _15_arraySeq = _nw3;
      ((this).box()).Put(_15_arraySeq);
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
