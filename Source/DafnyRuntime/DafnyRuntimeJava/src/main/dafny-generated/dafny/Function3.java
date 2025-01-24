package dafny;

@FunctionalInterface
public interface Function3<T0, T1, T2, T3> {
  public T3 apply(T0 t0, T1 t1, T2 t2);
  @SuppressWarnings({"unchecked", "deprecation"})
  public static <T0, T1, T2, T3> dafny.TypeDescriptor<Function3<T0, T1, T2, T3>> _typeDescriptor(dafny.TypeDescriptor<T0> t0, dafny.TypeDescriptor<T1> t1, dafny.TypeDescriptor<T2> t2, dafny.TypeDescriptor<T3> t3) {
    return (dafny.TypeDescriptor<Function3<T0, T1, T2, T3>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.reference(Function3.class);}
}
