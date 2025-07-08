package dafny;

@FunctionalInterface
public interface Function1<T0, T1> {
  public T1 apply(T0 t0);
  @SuppressWarnings({"unchecked", "deprecation"})
  public static <T0, T1> dafny.TypeDescriptor<Function1<T0, T1>> _typeDescriptor(dafny.TypeDescriptor<T0> t0, dafny.TypeDescriptor<T1> t1) {
    return (dafny.TypeDescriptor<Function1<T0, T1>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.reference(Function1.class);}
}
