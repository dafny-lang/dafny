package dafny;

public final class Array2<T> {
  public final Object[] elmts;
  private final dafny.TypeDescriptor<T> elmtType;
  public final int dim0;
  public final int dim1;
  public Array2(dafny.TypeDescriptor<T> elmtType, int dim0, int dim1, Object[] elmts) {
    assert elmts.getClass().isArray();
    this.elmtType = elmtType;
    this.dim0 = dim0;
    this.dim1 = dim1;
    this.elmts = elmts;
  }
  public T get(int i0, int i1) {
    return elmtType.getArrayElement(elmts[i0], i1);
  }
  public void set(int i0, int i1, T value) {
    elmtType.setArrayElement(elmts[i0], i1, value);
  }
  public void fill(T z) {
    for(int i0 = 0; i0 < dim0; i0++) {
      elmtType.fillArray(elmts[i0], z);
    }
  }
  public Array2 fillThenReturn(T z) {
    fill(z);
    return this;
  }
  @SuppressWarnings({"unchecked", "deprecation"})
  private static final dafny.TypeDescriptor<Array2<?>> TYPE = (dafny.TypeDescriptor<Array2<?>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.reference(Array2.class);
  @SuppressWarnings({"unchecked", "deprecation"})
  public static <T> dafny.TypeDescriptor<Array2<T>> _typeDescriptor() {
    return (dafny.TypeDescriptor<Array2<T>>) (dafny.TypeDescriptor<?>) TYPE;
  }
}
