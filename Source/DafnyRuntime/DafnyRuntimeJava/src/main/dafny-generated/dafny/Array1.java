package dafny;

public final class Array1<T> {
  public final Object elmts;
  private final dafny.TypeDescriptor<T> elmtType;
  public final int dim0;
  public Array1(dafny.TypeDescriptor<T> elmtType, int dim0, Object elmts) {
    assert elmts.getClass().isArray();
    this.elmtType = elmtType;
    this.dim0 = dim0;
    this.elmts = elmts;
  }
  public T get(int i0) {
    return elmtType.getArrayElement(elmts, i0);
  }
  public void set(int i0, T value) {
    elmtType.setArrayElement(elmts, i0, value);
  }
  public void fill(T z) {
    elmtType.fillArray(elmts, z);
  }
  public Array1 fillThenReturn(T z) {
    fill(z);
    return this;
  }
  @SuppressWarnings({"unchecked", "deprecation"})
  private static final dafny.TypeDescriptor<Array1<?>> TYPE = (dafny.TypeDescriptor<Array1<?>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.reference(Array1.class);
  @SuppressWarnings({"unchecked", "deprecation"})
  public static <T> dafny.TypeDescriptor<Array1<T>> _typeDescriptor() {
    return (dafny.TypeDescriptor<Array1<T>>) (dafny.TypeDescriptor<?>) TYPE;
  }
}
