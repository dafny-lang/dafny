package dafny;

public final class Array7<T> {
  public final Object[][][][][][] elmts;
  private final dafny.TypeDescriptor<T> elmtType;
  public final int dim0;
  public final int dim1;
  public final int dim2;
  public final int dim3;
  public final int dim4;
  public final int dim5;
  public final int dim6;
  public Array7(dafny.TypeDescriptor<T> elmtType, int dim0, int dim1, int dim2, int dim3, int dim4, int dim5, int dim6, Object[][][][][][] elmts) {
    assert elmts.getClass().isArray();
    this.elmtType = elmtType;
    this.dim0 = dim0;
    this.dim1 = dim1;
    this.dim2 = dim2;
    this.dim3 = dim3;
    this.dim4 = dim4;
    this.dim5 = dim5;
    this.dim6 = dim6;
    this.elmts = elmts;
  }
  public T get(int i0, int i1, int i2, int i3, int i4, int i5, int i6) {
    return elmtType.getArrayElement(elmts[i0][i1][i2][i3][i4][i5], i6);
  }
  public void set(int i0, int i1, int i2, int i3, int i4, int i5, int i6, T value) {
    elmtType.setArrayElement(elmts[i0][i1][i2][i3][i4][i5], i6, value);
  }
  public void fill(T z) {
    for(int i0 = 0; i0 < dim0; i0++) {
      for(int i1 = 0; i1 < dim1; i1++) {
        for(int i2 = 0; i2 < dim2; i2++) {
          for(int i3 = 0; i3 < dim3; i3++) {
            for(int i4 = 0; i4 < dim4; i4++) {
              for(int i5 = 0; i5 < dim5; i5++) {
                elmtType.fillArray(elmts[i0][i1][i2][i3][i4][i5], z);
              }
            }
          }
        }
      }
    }
  }
  public Array7 fillThenReturn(T z) {
    fill(z);
    return this;
  }
  @SuppressWarnings({"unchecked", "deprecation"})
  private static final dafny.TypeDescriptor<Array7<?>> TYPE = (dafny.TypeDescriptor<Array7<?>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.reference(Array7.class);
  @SuppressWarnings({"unchecked", "deprecation"})
  public static <T> dafny.TypeDescriptor<Array7<T>> _typeDescriptor() {
    return (dafny.TypeDescriptor<Array7<T>>) (dafny.TypeDescriptor<?>) TYPE;
  }
}
