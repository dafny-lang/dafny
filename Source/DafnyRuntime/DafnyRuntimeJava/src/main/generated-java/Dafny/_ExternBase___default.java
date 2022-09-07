// Class _ExternBase___default
// Dafny class __default compiled into Java
package Dafny;


@SuppressWarnings({"unchecked", "deprecation"})
public abstract class _ExternBase___default {
  public _ExternBase___default() {
  }
  public static <__T> void AppendRecursive(dafny.TypeDescriptor<__T> _td___T, Vector<__T> builder, Sequence<__T> e)
  {
    if (dafny.Helpers.<Sequence<__T>, Boolean>Let(e, _is_0 -> _is_0 instanceof ConcatSequence)) {
      ConcatSequence<__T> _16_concat;
      _16_concat = ((ConcatSequence<__T>)(e));
      __default.<__T>AppendRecursive(_td___T, builder, (_16_concat).left());
      __default.<__T>AppendRecursive(_td___T, builder, (_16_concat).right());
    } else if (dafny.Helpers.<Sequence<__T>, Boolean>Let(e, _is_1 -> _is_1 instanceof LazySequence)) {
      LazySequence<__T> _17_lazy;
      _17_lazy = ((LazySequence<__T>)(e));
      Sequence<__T> _18_boxed;
      Sequence<__T> _out33;
      _out33 = ((_17_lazy).box()).Get();
      _18_boxed = _out33;
      __default.<__T>AppendRecursive(_td___T, builder, _18_boxed);
    } else {
      ImmutableArray<__T> _19_a;
      ImmutableArray<__T> _out34;
      _out34 = (e).ToArray();
      _19_a = _out34;
      (builder).Append(_19_a);
    }
  }
  public static <__T> void AppendOptimized(dafny.TypeDescriptor<__T> _td___T, Vector<__T> builder, Sequence<__T> e, Vector<Sequence<__T>> stack)
  {
    TAIL_CALL_START: while (true) {
      if(true) {
        if (dafny.Helpers.<Sequence<__T>, Boolean>Let(e, _is_2 -> _is_2 instanceof ConcatSequence)) {
          ConcatSequence<__T> _20_concat;
          _20_concat = ((ConcatSequence<__T>)(e));
          (stack).AddLast((_20_concat).right());
          Vector<__T> _in0 = builder;
          Sequence<__T> _in1 = (_20_concat).left();
          Vector<Sequence<__T>> _in2 = stack;
          builder = _in0;
          e = _in1;
          stack = _in2;
          continue TAIL_CALL_START;
        } else if (dafny.Helpers.<Sequence<__T>, Boolean>Let(e, _is_3 -> _is_3 instanceof LazySequence)) {
          LazySequence<__T> _21_lazy;
          _21_lazy = ((LazySequence<__T>)(e));
          Sequence<__T> _22_boxed;
          Sequence<__T> _out35;
          _out35 = ((_21_lazy).box()).Get();
          _22_boxed = _out35;
          Vector<__T> _in3 = builder;
          Sequence<__T> _in4 = _22_boxed;
          Vector<Sequence<__T>> _in5 = stack;
          builder = _in3;
          e = _in4;
          stack = _in5;
          continue TAIL_CALL_START;
        } else if (dafny.Helpers.<Sequence<__T>, Boolean>Let(e, _is_4 -> _is_4 instanceof ArraySequence)) {
          ArraySequence<__T> _23_a;
          _23_a = ((ArraySequence<__T>)(e));
          (builder).Append((_23_a).value());
          if ((stack.size).signum() == 1) {
            Sequence<__T> _24_next;
            Sequence<__T> _out36;
            _out36 = (stack).RemoveLast();
            _24_next = _out36;
            Vector<__T> _in6 = builder;
            Sequence<__T> _in7 = _24_next;
            Vector<Sequence<__T>> _in8 = stack;
            builder = _in6;
            e = _in7;
            stack = _in8;
            continue TAIL_CALL_START;
          }
        } else {
        }
      }
      return;
    }
  }
  public static <__T> boolean EqualUpTo(dafny.TypeDescriptor<__T> _td___T, Sequence<__T> left, Sequence<__T> right, java.math.BigInteger index)
  {
    boolean ret = false;
    java.math.BigInteger _hi2 = index;
    for (java.math.BigInteger _25_i = java.math.BigInteger.ZERO; _25_i.compareTo(_hi2) < 0; _25_i = _25_i.add(java.math.BigInteger.ONE)) {
      @SuppressWarnings({"unchecked", "deprecation"})
      __T _26_leftElement;
      @SuppressWarnings({"unchecked", "deprecation"})
      __T _out37;
      _out37 = (left).Select(_25_i);
      _26_leftElement = _out37;
      @SuppressWarnings({"unchecked", "deprecation"})
      __T _27_rightElement;
      @SuppressWarnings({"unchecked", "deprecation"})
      __T _out38;
      _out38 = (right).Select(_25_i);
      _27_rightElement = _out38;
      if (!java.util.Objects.equals(_26_leftElement, _27_rightElement)) {
        ret = false;
        return ret;
      }
    }
    ret = true;
    return ret;
  }
  public static <__T> boolean EqualSequences(dafny.TypeDescriptor<__T> _td___T, Sequence<__T> left, Sequence<__T> right)
  {
    boolean ret = false;
    if(true) {
      if (!java.util.Objects.equals((left).Length(), (right).Length())) {
        ret = false;
        return ret;
      }
      boolean _out39;
      _out39 = __default.<__T>EqualUpTo(_td___T, left, right, (left).Length());
      ret = _out39;
    }
    return ret;
  }
  public static <__T> boolean IsPrefixOf(dafny.TypeDescriptor<__T> _td___T, Sequence<__T> left, Sequence<__T> right)
  {
    boolean ret = false;
    if(true) {
      if (((right).Length()).compareTo(((left).Length())) < 0) {
        ret = false;
        return ret;
      }
      boolean _out40;
      _out40 = __default.<__T>EqualUpTo(_td___T, left, right, (left).Length());
      ret = _out40;
    }
    return ret;
  }
  public static <__T> boolean IsProperPrefixOf(dafny.TypeDescriptor<__T> _td___T, Sequence<__T> left, Sequence<__T> right)
  {
    boolean ret = false;
    if(true) {
      if (((right).Length()).compareTo(((left).Length())) <= 0) {
        ret = false;
        return ret;
      }
      boolean _out41;
      _out41 = __default.<__T>EqualUpTo(_td___T, left, right, (left).Length());
      ret = _out41;
    }
    return ret;
  }
  public static <__T> boolean Contains(dafny.TypeDescriptor<__T> _td___T, Sequence<__T> s, __T t)
  {
    boolean _hresult = false;
    java.math.BigInteger _hi3 = (s).Length();
    for (java.math.BigInteger _28_i = java.math.BigInteger.ZERO; _28_i.compareTo(_hi3) < 0; _28_i = _28_i.add(java.math.BigInteger.ONE)) {
      @SuppressWarnings({"unchecked", "deprecation"})
      __T _29_element;
      @SuppressWarnings({"unchecked", "deprecation"})
      __T _out42;
      _out42 = (s).Select(_28_i);
      _29_element = _out42;
      if (java.util.Objects.equals(_29_element, t)) {
        _hresult = true;
        return _hresult;
      }
    }
    _hresult = false;
    return _hresult;
  }
  public static <__T> Sequence<__T> Concatenate(dafny.TypeDescriptor<__T> _td___T, Sequence<__T> left, Sequence<__T> right)
  {
    Sequence<__T> ret = null;
    if(true) {
      ConcatSequence<__T> _30_c;
      ConcatSequence<__T> _nw4 = new ConcatSequence<__T>(_td___T);
      _nw4.__ctor(left, right);
      _30_c = _nw4;
      LazySequence<__T> _nw5 = new LazySequence<__T>(_td___T);
      _nw5.__ctor(_30_c);
      ret = _nw5;
    }
    return ret;
  }
  public static <__T> Sequence<__T> Update(dafny.TypeDescriptor<__T> _td___T, Sequence<__T> s, java.math.BigInteger i, __T t)
  {
    Sequence<__T> ret = null;
    if(true) {
      ImmutableArray<__T> _31_a;
      ImmutableArray<__T> _out43;
      _out43 = (s).ToArray();
      _31_a = _out43;
      Array<__T> _32_newValue;
      Array<__T> _out44;
      _out44 = __default.<__T>CopyArray(_td___T, _31_a);
      _32_newValue = _out44;
      (_32_newValue).Update(i, t);
      ImmutableArray<__T> _33_newValueFrozen;
      ImmutableArray<__T> _out45;
      _out45 = (_32_newValue).Freeze((_32_newValue).Length());
      _33_newValueFrozen = _out45;
      ArraySequence<__T> _nw6 = new ArraySequence<__T>(_td___T);
      _nw6.__ctor(_33_newValueFrozen);
      ret = _nw6;
    }
    return ret;
  }
  public static void MultiDimentionalArrays()
  {
    dafny.Array3<java.math.BigInteger> _34_a;
    dafny.Array3<java.math.BigInteger> _nw7 = new dafny.Array3<>(dafny.TypeDescriptor.BIG_INTEGER, dafny.Helpers.toIntChecked((java.math.BigInteger.valueOf(3L)), "Java arrays may be no larger than the maximum 32-bit signed int"), dafny.Helpers.toIntChecked((java.math.BigInteger.valueOf(4L)), "Java arrays may be no larger than the maximum 32-bit signed int"), dafny.Helpers.toIntChecked((java.math.BigInteger.valueOf(5L)), "Java arrays may be no larger than the maximum 32-bit signed int"), (Object[][]) dafny.TypeDescriptor.BIG_INTEGER.newArray(dafny.Helpers.toIntChecked((java.math.BigInteger.valueOf(3L)), "Java arrays may be no larger than the maximum 32-bit signed int"), dafny.Helpers.toIntChecked((java.math.BigInteger.valueOf(4L)), "Java arrays may be no larger than the maximum 32-bit signed int"), dafny.Helpers.toIntChecked((java.math.BigInteger.valueOf(5L)), "Java arrays may be no larger than the maximum 32-bit signed int")));
    dafny.Function3<java.math.BigInteger, java.math.BigInteger, java.math.BigInteger, java.math.BigInteger> _arrayinit0 = ((dafny.Function3<java.math.BigInteger, java.math.BigInteger, java.math.BigInteger, java.math.BigInteger>)(_35_i, _36_j, _37_k) -> {
      return java.math.BigInteger.ZERO;
    });
    for (java.math.BigInteger _arrayinit_00 = java.math.BigInteger.ZERO; _arrayinit_00.compareTo(java.math.BigInteger.valueOf(_nw7.dim0)) < 0; _arrayinit_00 = _arrayinit_00.add(java.math.BigInteger.ONE)) {
      for (java.math.BigInteger _arrayinit_10 = java.math.BigInteger.ZERO; _arrayinit_10.compareTo(java.math.BigInteger.valueOf(_nw7.dim1)) < 0; _arrayinit_10 = _arrayinit_10.add(java.math.BigInteger.ONE)) {
        for (java.math.BigInteger _arrayinit_20 = java.math.BigInteger.ZERO; _arrayinit_20.compareTo(java.math.BigInteger.valueOf(_nw7.dim2)) < 0; _arrayinit_20 = _arrayinit_20.add(java.math.BigInteger.ONE)) {
          ((java.math.BigInteger[][][]) (_nw7).elmts)[dafny.Helpers.toInt(_arrayinit_00)][dafny.Helpers.toInt(_arrayinit_10)][dafny.Helpers.toInt(_arrayinit_20)] = _arrayinit0.apply(_arrayinit_00, _arrayinit_10, _arrayinit_20);
        }
      }
    }
    _34_a = _nw7;
    ((java.math.BigInteger[][][]) (((_34_a)).elmts))[dafny.Helpers.toInt(((java.math.BigInteger.ONE)).intValue())][dafny.Helpers.toInt(((java.math.BigInteger.ONE)).intValue())][dafny.Helpers.toInt(((java.math.BigInteger.ONE)).intValue())] = java.math.BigInteger.valueOf(42L);
  }
  private static final dafny.TypeDescriptor<__default> _TYPE = dafny.TypeDescriptor.referenceWithInitializer(__default.class, () -> (__default) null);
  public static dafny.TypeDescriptor<__default> _typeDescriptor() {
    return (dafny.TypeDescriptor<__default>) (dafny.TypeDescriptor<?>) _TYPE;
  }
}
