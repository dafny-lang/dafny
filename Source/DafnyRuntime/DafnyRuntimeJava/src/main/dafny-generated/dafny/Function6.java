package dafny;

@FunctionalInterface
public interface Function6<T0, T1, T2, T3, T4, T5, T6> {
  public T6 apply(T0 t0, T1 t1, T2 t2, T3 t3, T4 t4, T5 t5);
  @SuppressWarnings({"unchecked", "deprecation"})
  public static <T0, T1, T2, T3, T4, T5, T6> dafny.TypeDescriptor<Function6<T0, T1, T2, T3, T4, T5, T6>> _typeDescriptor(dafny.TypeDescriptor<T0> t0, dafny.TypeDescriptor<T1> t1, dafny.TypeDescriptor<T2> t2, dafny.TypeDescriptor<T3> t3, dafny.TypeDescriptor<T4> t4, dafny.TypeDescriptor<T5> t5, dafny.TypeDescriptor<T6> t6) {
    return (dafny.TypeDescriptor<Function6<T0, T1, T2, T3, T4, T5, T6>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.reference(Function6.class);}
}
