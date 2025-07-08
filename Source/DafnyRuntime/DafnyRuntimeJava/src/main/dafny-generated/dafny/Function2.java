package dafny;

@FunctionalInterface
public interface Function2<T0, T1, T2> {
  public T2 apply(T0 t0, T1 t1);
  @SuppressWarnings({"unchecked", "deprecation"})
  public static <T0, T1, T2> dafny.TypeDescriptor<Function2<T0, T1, T2>> _typeDescriptor(dafny.TypeDescriptor<T0> t0, dafny.TypeDescriptor<T1> t1, dafny.TypeDescriptor<T2> t2) {
    return (dafny.TypeDescriptor<Function2<T0, T1, T2>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.reference(Function2.class);}
}
