package dafny;

@FunctionalInterface
public interface Function0<T0> {
  public T0 apply();
  @SuppressWarnings({"unchecked", "deprecation"})
  public static <T0> dafny.TypeDescriptor<Function0<T0>> _typeDescriptor(dafny.TypeDescriptor<T0> t0) {
    return (dafny.TypeDescriptor<Function0<T0>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.reference(Function0.class);}
}
