// Class _ExternBase___default
// Dafny class __default compiled into Java
package Dafny;


@SuppressWarnings({"unchecked", "deprecation"})
public abstract class _ExternBase___default {
  public _ExternBase___default() {
  }
  public static <__T> Sequence<__T> Concatenate(dafny.TypeDescriptor<__T> _td___T, Sequence<__T> left, Sequence<__T> right)
  {
    Sequence<__T> ret = null;
    if(true) {
      ConcatSequence<__T> _12_c;
      ConcatSequence<__T> _nw4 = new ConcatSequence<__T>(_td___T);
      _nw4.__ctor(left, right);
      _12_c = _nw4;
      LazySequence<__T> _nw5 = new LazySequence<__T>(_td___T);
      _nw5.__ctor(_12_c);
      ret = _nw5;
    }
    return ret;
  }
  public static <__T> void AppendRecursive(dafny.TypeDescriptor<__T> _td___T, Vector<__T> builder, Sequence<__T> e)
  {
    if (dafny.Helpers.<Sequence<__T>, Boolean>Let(e, _is_0 -> _is_0 instanceof ConcatSequence)) {
      ConcatSequence<__T> _13_concat;
      _13_concat = ((ConcatSequence<__T>)(e));
      __default.<__T>AppendRecursive(_td___T, builder, (_13_concat).left());
      __default.<__T>AppendRecursive(_td___T, builder, (_13_concat).right());
    } else if (dafny.Helpers.<Sequence<__T>, Boolean>Let(e, _is_1 -> _is_1 instanceof LazySequence)) {
      LazySequence<__T> _14_lazy;
      _14_lazy = ((LazySequence<__T>)(e));
      Sequence<__T> _15_boxed;
      Sequence<__T> _out25;
      _out25 = ((_14_lazy).box()).Get();
      _15_boxed = _out25;
      __default.<__T>AppendRecursive(_td___T, builder, _15_boxed);
    } else {
      ImmutableArray<__T> _16_a;
      ImmutableArray<__T> _out26;
      _out26 = (e).ToArray();
      _16_a = _out26;
      (builder).Append(_16_a);
    }
  }
  public static <__T> void AppendOptimized(dafny.TypeDescriptor<__T> _td___T, Vector<__T> builder, Sequence<__T> e, Vector<Sequence<__T>> stack)
  {
    TAIL_CALL_START: while (true) {
      if(true) {
        if (dafny.Helpers.<Sequence<__T>, Boolean>Let(e, _is_2 -> _is_2 instanceof ConcatSequence)) {
          ConcatSequence<__T> _17_concat;
          _17_concat = ((ConcatSequence<__T>)(e));
          (stack).AddLast((_17_concat).right());
          Vector<__T> _in0 = builder;
          Sequence<__T> _in1 = (_17_concat).left();
          Vector<Sequence<__T>> _in2 = stack;
          builder = _in0;
          e = _in1;
          stack = _in2;
          continue TAIL_CALL_START;
        } else if (dafny.Helpers.<Sequence<__T>, Boolean>Let(e, _is_3 -> _is_3 instanceof LazySequence)) {
          LazySequence<__T> _18_lazy;
          _18_lazy = ((LazySequence<__T>)(e));
          Sequence<__T> _19_boxed;
          Sequence<__T> _out27;
          _out27 = ((_18_lazy).box()).Get();
          _19_boxed = _out27;
          Vector<__T> _in3 = builder;
          Sequence<__T> _in4 = _19_boxed;
          Vector<Sequence<__T>> _in5 = stack;
          builder = _in3;
          e = _in4;
          stack = _in5;
          continue TAIL_CALL_START;
        } else if (dafny.Helpers.<Sequence<__T>, Boolean>Let(e, _is_4 -> _is_4 instanceof ArraySequence)) {
          ArraySequence<__T> _20_a;
          _20_a = ((ArraySequence<__T>)(e));
          (builder).Append((_20_a).value());
          if ((stack.size).signum() == 1) {
            Sequence<__T> _21_next;
            Sequence<__T> _out28;
            _out28 = (stack).RemoveLast();
            _21_next = _out28;
            Vector<__T> _in6 = builder;
            Sequence<__T> _in7 = _21_next;
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
  private static final dafny.TypeDescriptor<__default> _TYPE = dafny.TypeDescriptor.referenceWithInitializer(__default.class, () -> (__default) null);
  public static dafny.TypeDescriptor<__default> _typeDescriptor() {
    return (dafny.TypeDescriptor<__default>) (dafny.TypeDescriptor<?>) _TYPE;
  }
}
