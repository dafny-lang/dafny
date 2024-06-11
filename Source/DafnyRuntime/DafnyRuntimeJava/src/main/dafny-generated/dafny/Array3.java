package dafny;

public final class Array3<T> {
  public final Object[][] elmts;
  private final dafny.TypeDescriptor<T> elmtType;
  public final int dim0;
  public final int dim1;
  public final int dim2;
  public Array3(dafny.TypeDescriptor<T> elmtType, int dim0, int dim1, int dim2, Object[][] elmts) {
    assert elmts.getClass().isArray();
    this.elmtType = elmtType;
    this.dim0 = dim0;
    this.dim1 = dim1;
    this.dim2 = dim2;
    this.elmts = elmts;
  }
  public T get(int i0, int i1, int i2) {
    return elmtType.getArrayElement(elmts[i0][i1], i2);
  }
  public void set(int i0, int i1, int i2, T value) {
    elmtType.setArrayElement(elmts[i0][i1], i2, value);
  }
  public void fill(T z) {
    for(int i0 = 0; i0 < dim0; i0++) {
      for(int i1 = 0; i1 < dim1; i1++) {
        elmtType.fillArray(elmts[i0][i1], z);
      }
    }
  }
  public Array3 fillThenReturn(T z) {
    fill(z);
    return this;
  }
  @SuppressWarnings({"unchecked", "deprecation"})
  private static final dafny.TypeDescriptor<Array3<?>> TYPE = (dafny.TypeDescriptor<Array3<?>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.reference(Array3.class);
  @SuppressWarnings({"unchecked", "deprecation"})
  public static <T> dafny.TypeDescriptor<Array3<T>> _typeDescriptor() {
    return (dafny.TypeDescriptor<Array3<T>>) (dafny.TypeDescriptor<?>) TYPE;
  }
}
