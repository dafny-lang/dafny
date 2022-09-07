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
  public int HashCode()
  {
    int _out17;
    _out17 = Dafny._Companion_Sequence.<T>HashCode(_td_T, this);
    return _out17;
  }
  public dafny.DafnySequence<? extends Character> ToString()
  {
    dafny.DafnySequence<? extends Character> _out18;
    _out18 = Dafny._Companion_Sequence.<T>ToString(_td_T, this);
    return _out18;
  }
  public T Select(java.math.BigInteger index)
  {
    @SuppressWarnings({"unchecked", "deprecation"})
    T _out19;
    _out19 = Dafny._Companion_Sequence.<T>Select(_td_T, this, index);
    return _out19;
  }
  public Sequence<T> Drop(java.math.BigInteger lo)
  {
    Sequence<T> _out20;
    _out20 = Dafny._Companion_Sequence.<T>Drop(_td_T, this, lo);
    return _out20;
  }
  public Sequence<T> Take(java.math.BigInteger hi)
  {
    Sequence<T> _out21;
    _out21 = Dafny._Companion_Sequence.<T>Take(_td_T, this, hi);
    return _out21;
  }
  public Sequence<T> Subsequence(java.math.BigInteger lo, java.math.BigInteger hi)
  {
    Sequence<T> _out22;
    _out22 = Dafny._Companion_Sequence.<T>Subsequence(_td_T, this, lo, hi);
    return _out22;
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
      Vector<T> _11_builder;
      Vector<T> _nw1 = new Vector<T>(_td_T);
      _nw1.__ctor((this).length());
      _11_builder = _nw1;
      Vector<Sequence<T>> _12_stack;
      Vector<Sequence<T>> _nw2 = new Vector<Sequence<T>>(Dafny._Companion_Sequence.<T>_typeDescriptor(_td_T));
      _nw2.__ctor(java.math.BigInteger.valueOf(10L));
      _12_stack = _nw2;
      __default.<T>AppendOptimized(_td_T, _11_builder, this, _12_stack);
      ImmutableArray<T> _out23;
      _out23 = (_11_builder).Freeze();
      ret = _out23;
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
