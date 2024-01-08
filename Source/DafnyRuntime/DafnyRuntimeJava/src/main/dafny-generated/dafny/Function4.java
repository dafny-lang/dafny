package dafny;

@FunctionalInterface
public interface Function4<T0, T1, T2, T3, T4> {
  public T4 apply(T0 t0, T1 t1, T2 t2, T3 t3);
  @SuppressWarnings({"unchecked", "deprecation"})
  public static <T0, T1, T2, T3, T4> dafny.TypeDescriptor<Function4<T0, T1, T2, T3, T4>> _typeDescriptor(dafny.TypeDescriptor<T0> t0, dafny.TypeDescriptor<T1> t1, dafny.TypeDescriptor<T2> t2, dafny.TypeDescriptor<T3> t3, dafny.TypeDescriptor<T4> t4) {
    return (dafny.TypeDescriptor<Function4<T0, T1, T2, T3, T4>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.reference(Function4.class);}
}
